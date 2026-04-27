MACHINE Checkers

SETS
    PLAYER = {white, black};
    TYPE = {man, king};
    STATUS = {playing, white_won, black_won}

CONSTANTS
    playableBoard,
    whiteInit,
    blackInit

PROPERTIES
    playableBoard = {xx,yy | xx:1..8 & yy:1..8 & (xx+yy) mod 2 = 0} &
    whiteInit = {xx,yy | xx:1..3 & yy:1..8 & (xx+yy) mod 2 = 0} &
    blackInit = {xx,yy | xx:6..8 & yy:1..8 & (xx+yy) mod 2 = 0}

VARIABLES
    board,
    turn,
    gameStatus

INVARIANT
    board : playableBoard +-> (PLAYER * TYPE) &
    turn : PLAYER &
    gameStatus : STATUS

INITIALISATION
    board := 
        (whiteInit * {(white |-> man)}) \/ 
        (blackInit * {(black |-> man)})
    ||
    turn := white 
    ||
    gameStatus := playing

OPERATIONS

move(fromX, fromY, toX, toY) =
PRE
    fromX:1..8 & fromY:1..8 & toX:1..8 & toY:1..8 &

    (fromX |-> fromY) : dom(board) &
    (toX |-> toY) : playableBoard &
    (toX |-> toY) /: dom(board) &

    board(fromX,fromY) : {turn} * TYPE &

    (
        /* peça normal */
        (
            board(fromX,fromY) = (turn |-> man) &
            
            max({fromX - toX, toX - fromX}) = 1 &
            max({fromY - toY, toY - fromY}) = 1 &

            /* checa se é um movimento de uma casa */
            ((turn = white & toX = fromX + 1) or (turn = black & toX = fromX - 1))
        )

        or

        /* peça dama */
        (
            board(fromX,fromY) = (turn |-> king) &
            
            max({fromX - toX, toX - fromX}) = max({fromY - toY, toY - fromY}) &

            /* checa se o caminho está livre */
            !(pathX, pathY).(
                pathX:1..8 & pathY:1..8 &
                
                min({fromX, toX}) < pathX &
                pathX < max({fromX, toX}) &
                
                min({fromY, toY}) < pathY &
                pathY < max({fromY, toY}) &
                
                max({fromX - pathX, pathX - fromX}) = max({fromY - pathY, pathY - fromY}) & 
                
                (pathX |-> pathY) : playableBoard
                =>
                (pathX |-> pathY) /: dom(board)
            )
        )
    )

THEN

    /* promoção */
    IF board(fromX,fromY) = (turn |-> man) &
       ((turn = white & toX = 8) or (turn = black & toX = 1))
    THEN
        board :=
            ({(fromX |-> fromY)} <<| board) <+
            {(toX |-> toY) |-> (turn |-> king)}
    ELSE
        board :=
            ({(fromX |-> fromY)} <<| board) <+
            {(toX |-> toY) |-> board(fromX,fromY)}
    END

    ||

    /* troca turno */
    IF turn = white THEN
        turn := black
    ELSE
        turn := white
    END

END;

current_status <-- checkWinner =
BEGIN
    /* não tem peças pretas no tabuleiro */
    IF ran(board) /\ ({black} * TYPE) = {} THEN
        current_status := white_won    
    /* não tem peças brancas no tabuleiro */ 
    ELSIF ran(board) /\ ({white} * TYPE) = {} THEN
        current_status := black_won
    ELSE
        current_status := playing
    END
END

END