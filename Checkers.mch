MACHINE Checkers
    
SETS
    PLAYER = {white, black};
    TYPE = {man, king};
    STATUS = {playing, white_won, black_won}
    
CONSTANTS
    playableBoard,
    whiteInit,
    blackInit,
    mkPair,
    absDiff,
    opponent
    
PROPERTIES
    playableBoard = {xx,yy | xx:1..8 & yy:1..8 & (xx+yy) mod 2 = 0} &
    whiteInit = {xx,yy | xx:1..3 & yy:1..8 & (xx+yy) mod 2 = 0} &
    blackInit = {xx,yy | xx:6..8 & yy:1..8 & (xx+yy) mod 2 = 0} &
    mkPair = %(xx,yy) . (xx:INTEGER & yy:INTEGER | xx |-> yy) &
    absDiff = %(nn, mm) . (nn:INTEGER & mm:INTEGER | max({nn - mm, mm - nn})) &
    opponent = {white |-> black, black |-> white}

VARIABLES
    board,
    turn,
    gameStatus,
    comboPiece 
    
INVARIANT
    board : playableBoard +-> (PLAYER * TYPE) &
    turn : PLAYER &
    gameStatus : STATUS &
    comboPiece <: playableBoard &
    card(comboPiece) <= 1
    
INITIALISATION
    board := 
    (whiteInit * {(white |-> man)}) \/ 
    (blackInit * {(black |-> man)})
    ||
    turn::PLAYER
    ||
    gameStatus := playing
    ||
    comboPiece := {}
    
OPERATIONS
    
    move(fromX, fromY, toX, toY) =
    PRE
        gameStatus = playing &
        fromX:1..8 & fromY:1..8 & toX:1..8 & toY:1..8 &
        
        mkPair(fromX, fromY) : dom(board) &
        mkPair(toX, toY) : playableBoard &
        mkPair(toX, toY) /: dom(board) &
        board(mkPair(fromX, fromY)) : {turn} * TYPE &
        
        comboPiece = {} & /* não pode fazer movimento normal no meio de um combo */
        
        /* checa se há capturas a serem feitas */
        !(px, py, tx, ty, cx, cy).(
            px:1..8 & py:1..8 & tx:1..8 & ty:1..8 & cx:1..8 & cy:1..8 &
            mkPair(px, py) : dom(board) & 
            board(mkPair(px, py)) : {turn} * TYPE &
            mkPair(tx, ty) : playableBoard & 
            mkPair(tx, ty) /: dom(board) &
            mkPair(cx, cy) : dom(board) & 
            board(mkPair(cx, cy)) : {opponent(turn)} * TYPE
            =>
            (
                not(
                    board(mkPair(px, py)) = (turn |-> man) & 
                    absDiff(px, tx) = 2 & absDiff(py, ty) = 2 & 
                    cx * 2 = px + tx & cy * 2 = py + ty
                )
                &
                not(
                    board(mkPair(px, py)) = (turn |-> king) & 
                    absDiff(px, tx) = absDiff(py, ty) & 
                    min({px, tx}) < cx & cx < max({px, tx}) & 
                    min({py, ty}) < cy & cy < max({py, ty}) & 
                    absDiff(px, cx) = absDiff(py, cy) & 
                    !(pathX, pathY).(
                        pathX:1..8 & pathY:1..8 & 
                        min({px, tx}) < pathX & pathX < max({px, tx}) & 
                        min({py, ty}) < pathY & pathY < max({py, ty}) & 
                        absDiff(px, pathX) = absDiff(py, pathY) & 
                        not(pathX = cx & pathY = cy) 
                        => mkPair(pathX, pathY) /: dom(board)
                    )
                )
            )
        ) &
        (
            /* movimento do peão */
            (
                board(mkPair(fromX, fromY)) = (turn |-> man) &
                absDiff(fromX, toX) = 1 & absDiff(fromY, toY) = 1 &
                ((turn = white & toX = fromX + 1) or (turn = black & toX = fromX - 1))
            )
            or
            /* movimento da dama */
            (
                board(mkPair(fromX,fromY)) = (turn |-> king) &
                absDiff(fromX, toX) = absDiff(fromY, toY) &
                !(pathX, pathY).(
                    pathX:1..8 & pathY:1..8 &
                    min({fromX, toX}) < pathX & pathX < max({fromX, toX}) &
                    min({fromY, toY}) < pathY & pathY < max({fromY, toY}) &
                    absDiff(fromX, pathX) = absDiff(fromY, pathY) 
                    =>
                    mkPair(pathX, pathY) /: dom(board) 
                )
            )
        )
    THEN
        IF board(mkPair(fromX, fromY)) = (turn |-> man) & ((turn = white & toX = 8) or (turn = black & toX = 1)) THEN
            board := (board - ({mkPair(fromX, fromY)} <| board)) \/ {mkPair(toX, toY) |-> (turn |-> king)}
        ELSE
            board := (board - ({mkPair(fromX, fromY)} <| board)) \/ {mkPair(toX, toY) |-> board(mkPair(fromX, fromY))}
        END
        ||
        turn := opponent(turn) 
    END;

    capture(fromX, fromY, toX, toY, capX, capY) =
    PRE
        gameStatus = playing &
        fromX:1..8 & fromY:1..8 & toX:1..8 & toY:1..8 & capX:1..8 & capY:1..8 &
        
        mkPair(fromX, fromY) : dom(board) &
        mkPair(toX, toY) : playableBoard & mkPair(toX, toY) /: dom(board) &
        board(mkPair(fromX, fromY)) : {turn} * TYPE &
        
        mkPair(capX, capY) : dom(board) &
        board(mkPair(capX, capY)) : {opponent(turn)} * TYPE &
        
        (comboPiece /= {} => mkPair(fromX, fromY) : comboPiece) &
        (
            /* pulo do peão */
            (
                board(mkPair(fromX, fromY)) = (turn |-> man) &
                absDiff(fromX, toX) = 2 & absDiff(fromY, toY) = 2 &
                capX * 2 = fromX + toX & capY * 2 = fromY + toY
            )
            or
            /* pulo da dama */
            (
                board(mkPair(fromX, fromY)) = (turn |-> king) &
                absDiff(fromX, toX) = absDiff(fromY, toY) &
                min({fromX, toX}) < capX & capX < max({fromX, toX}) &
                min({fromY, toY}) < capY & capY < max({fromY, toY}) &
                absDiff(fromX, capX) = absDiff(fromY, capY) &
                !(px, py).(
                    px:1..8 & py:1..8 & 
                    min({fromX, toX}) < px & px < max({fromX, toX}) & 
                    min({fromY, toY}) < py & py < max({fromY, toY}) &
                    absDiff(fromX, px) = absDiff(fromY, py) &
                    not(px = capX & py = capY)
                    => mkPair(px, py) /: dom(board)
                )
            )
        )
    THEN
        IF board(mkPair(fromX, fromY)) = (turn |-> man) & ((turn = white & toX = 8) or (turn = black & toX = 1)) THEN
            /* promove para dama e encerra */
            board := (board - ({mkPair(fromX, fromY), mkPair(capX, capY)} <| board)) \/ {mkPair(toX, toY) |-> (turn |-> king)}
            || turn := opponent(turn)
            || comboPiece := {}
        ELSE
            /* executa o pulo e come a peça */
            board := (board - ({mkPair(fromX, fromY), mkPair(capX, capY)} <| board)) \/ {mkPair(toX, toY) |-> board(mkPair(fromX, fromY))}
            ||
            IF 
                /* checa se peão pode comer mais peças */
                (board(mkPair(fromX, fromY)) = (turn |-> man) & 
                 #(ntx, nty, ncx, ncy).(
                     ntx:1..8 & nty:1..8 & ncx:1..8 & ncy:1..8 &

                     mkPair(ntx, nty) : playableBoard &
                     (mkPair(ntx, nty) /: dom(board) or (ntx = fromX & nty = fromY) or (ntx = capX & nty = capY)) &

                     absDiff(toX, ntx) = 2 & absDiff(toY, nty) = 2 &
                     ncx * 2 = toX + ntx & ncy * 2 = toY + nty &
                     mkPair(ncx, ncy) : dom(board) & 
                     board(mkPair(ncx, ncy)) : {opponent(turn)} * TYPE &
                     not(ncx = capX & ncy = capY) /* não pode ser a peça recém capturada */
                 )
                )
                or
                /* checa se a dama pode comer mais peças */
                (board(mkPair(fromX, fromY)) = (turn |-> king) & 
                 #(ntx, nty, ncx, ncy).(
                     ntx:1..8 & nty:1..8 & ncx:1..8 & ncy:1..8 &
                     mkPair(ntx, nty) : playableBoard &
                     (mkPair(ntx, nty) /: dom(board) or (ntx = fromX & nty = fromY) or (ntx = capX & nty = capY)) &
                     absDiff(toX, ntx) = absDiff(toY, nty) &

                     min({toX, ntx}) < ncx & ncx < max({toX, ntx}) &
                     min({toY, nty}) < ncy & ncy < max({toY, nty}) &
                     absDiff(toX, ncx) = absDiff(toY, ncy) &
                     mkPair(ncx, ncy) : dom(board) & 
                     board(mkPair(ncx, ncy)) : {opponent(turn)} * TYPE &

                     not(ncx = capX & ncy = capY) & /* não pode ser a peça recém capturada */

                     /* checa se o caminho da dama está livre */
                     !(px, py).(
                         px:1..8 & py:1..8 & 
                         min({toX, ntx}) < px & px < max({toX, ntx}) & 
                         min({toY, nty}) < py & py < max({toY, nty}) &
                         absDiff(toX, px) = absDiff(toY, py) &
                         not(px = ncx & py = ncy)
                         => 
                         (mkPair(px, py) /: dom(board) or (px = fromX & py = fromY) or (px = capX & py = capY))
                     )
                 )
                )
            THEN
                comboPiece := {mkPair(toX, toY)} /* tranca o turno na peça */
            ELSE
                turn := opponent(turn) /*passa a vez e limpa a trava */
                || comboPiece := {}
            END
        END
    END;

    current_status <-- checkWinner =
    BEGIN
        IF ran(board) /\ ({black} * TYPE) = {} THEN
            current_status := white_won    
        ELSIF ran(board) /\ ({white} * TYPE) = {} THEN
            current_status := black_won
        ELSE
            current_status := playing
        END
    END
    
END
