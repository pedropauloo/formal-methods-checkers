MACHINE Checkers
    
SETS
    PLAYER = {white, black};
    TYPE = {man, king};
    STATUS = {playing, white_won, black_won, draw}
    
CONSTANTS
    playableBoard,
    whiteInit,
    blackInit,
    mkPair,
    absDiff,
    opponent,
    turnToWon,

    captureBoard,
    drawBoard,
    victoryBoard
    
PROPERTIES
    playableBoard = {xx,yy | xx:1..8 & yy:1..8 & (xx+yy) mod 2 = 0} &
    whiteInit = {xx,yy | xx:1..3 & yy:1..8 & (xx+yy) mod 2 = 0} &
    blackInit = {xx,yy | xx:6..8 & yy:1..8 & (xx+yy) mod 2 = 0} &
    mkPair = %(xx,yy) . (xx:INTEGER & yy:INTEGER | xx |-> yy) &
    absDiff = %(nn, mm) . (nn:INTEGER & mm:INTEGER | max({nn - mm, mm - nn})) &
    opponent = {white |-> black, black |-> white} &
    turnToWon = {white |-> white_won, black |-> black_won} &

    captureBoard = { // Testes de captura
	    (3 |-> 3) |-> (black |-> man),
    	(4 |-> 4) |-> (white |-> man),
    	(4 |-> 8) |-> (black |-> man),
    	(5 |-> 5) |-> (black |-> man),
    	(5 |-> 7) |-> (black |-> man),
    	(7 |-> 3) |-> (black |-> man),
    	(7 |-> 5) |-> (black |-> man),
    	(7 |-> 7) |-> (black |-> man)
    } &
    drawBoard = { // Teste empate (começando pelas brancas)
        (2 |-> 2) |-> (black |-> man),
        (3 |-> 3) |-> (white |-> man),
        (4 |-> 4) |-> (black |-> man)
    } &
    victoryBoard = { // Testes de vitória
        (4 |-> 4) |-> (black |-> man),
        (5 |-> 5) |-> (white |-> man)
    }   
    
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
    comboPiece : FIN(comboPiece) &
    card(comboPiece) <= 1 &
    (
        (gameStatus = playing & card(board |> ({white} * TYPE)) > 0 & card(board |> ({black} * TYPE)) > 0) 
        or
        ((gameStatus = white_won & card(board |> ({black} * TYPE)) = 0) or (gameStatus = black_won & card(board |> ({white} * TYPE)) = 0))
        or
        (gameStatus = draw & card(board |> ({black} * TYPE)) = 1 & card(board |> ({white} * TYPE)) = 1)
    )
    
INITIALISATION
    CHOICE board:=
    	(whiteInit * {(white |-> man)}) \/ 
    	(blackInit * {(black |-> man)})
	    OR board := captureBoard
    	OR board := drawBoard
    	OR board := victoryBoard
	END
    ||
    turn::PLAYER // Permite que qualquer jogador comece o jogo
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
        
        comboPiece = {} & // Não pode fazer movimento normal no meio de um combo
        
        // Checa se há capturas a serem feitas
        // Caso exista movimento de captura, é obrigatório escolher entre um deles
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
            // Movimento do peão
            (
                board(mkPair(fromX, fromY)) = (turn |-> man) &
                absDiff(fromX, toX) = 1 & absDiff(fromY, toY) = 1 & // A posição destino é adjacente à origem
                ((turn = white & toX = fromX + 1) or (turn = black & toX = fromX - 1)) // As peças brancas "sobem" e as pretas "descem" no tabuleiro
            )
            or
            // Movimento da dama
            (
                board(mkPair(fromX,fromY)) = (turn |-> king) &
                absDiff(fromX, toX) = absDiff(fromY, toY) & // A posição destino está em uma das diagonais da origem
                !(pathX, pathY).(
                    pathX:1..8 & pathY:1..8 &
                    min({fromX, toX}) < pathX & pathX < max({fromX, toX}) &
                    min({fromY, toY}) < pathY & pathY < max({fromY, toY}) & // pathX, pathY está entre a origem e o destino
                    absDiff(fromX, pathX) = absDiff(fromY, pathY)
                    =>
                    mkPair(pathX, pathY) /: dom(board) // Todas as posições entre a origem e destino estão vazias
                )
            )
        )
    THEN
        IF board(mkPair(fromX, fromY)) = (turn |-> man) & ((turn = white & toX = 8) or (turn = black & toX = 1)) THEN
            board := ({mkPair(fromX, fromY)} <<| board) \/ {mkPair(toX, toY) |-> (turn |-> king)} // Promoção
        ELSE
            board := ({mkPair(fromX, fromY)} <<| board) \/ {mkPair(toX, toY) |-> board(mkPair(fromX, fromY))} // Movimento normal
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
        board(mkPair(fromX, fromY)) : {turn} * TYPE & // Peça a ser movida é do jogador a jogar
        
        mkPair(capX, capY) : dom(board) &
        board(mkPair(capX, capY)) : {opponent(turn)} * TYPE & // Peça a ser capturada é do oponente
        
        (comboPiece /= {} => mkPair(fromX, fromY) : comboPiece) & // Se a captura é múltipla, a origem do movimento atual é o destino da jogada anterior
        (
            // Pulo do peão
            (
                board(mkPair(fromX, fromY)) = (turn |-> man) &
                absDiff(fromX, toX) = 2 & absDiff(fromY, toY) = 2 &
                capX * 2 = fromX + toX & capY * 2 = fromY + toY // Posição de captura é o ponto médio entre a origem e o destino
            )
            or
            // Pulo da dama
            (
                board(mkPair(fromX, fromY)) = (turn |-> king) &
                absDiff(fromX, toX) = absDiff(fromY, toY) & // Diagonal
                min({fromX, toX}) < capX & capX < max({fromX, toX}) &
                min({fromY, toY}) < capY & capY < max({fromY, toY}) & // Captura está entre a origem e destino
                absDiff(fromX, capX) = absDiff(fromY, capY) &
                !(px, py).(
                    px:1..8 & py:1..8 & 
                    min({fromX, toX}) < px & px < max({fromX, toX}) & 
                    min({fromY, toY}) < py & py < max({fromY, toY}) &
                    absDiff(fromX, px) = absDiff(fromY, py) &
                    not(px = capX & py = capY) // Para toda posição entre a origem e destino que não é a da captura
                    => mkPair(px, py) /: dom(board) // A casa está vazia
                )
            )
        )
    THEN
        IF
            // Checa se peão pode comer mais peças
            (board(mkPair(fromX, fromY)) = (turn |-> man) & 
                #(ntx, nty, ncx, ncy).(
                    ntx:1..8 & nty:1..8 & ncx:1..8 & ncy:1..8 &
                    
                    mkPair(ntx, nty) : playableBoard &
                    (mkPair(ntx, nty) /: dom(board) & // or (ntx = fromX & nty = fromY) or (ntx = capX & nty = capY)) &
                    
                    absDiff(toX, ntx) = 2 & absDiff(toY, nty) = 2 &
                    ncx * 2 = toX + ntx & ncy * 2 = toY + nty &
                    mkPair(ncx, ncy) : dom(board) & 
                    board(mkPair(ncx, ncy)) : {opponent(turn)} * TYPE &
                    not(ncx = capX & ncy = capY) // Não pode ser a peça recém capturada
                )
            ))
            or
            // Checa se a dama pode comer mais peças
            (board(mkPair(fromX, fromY)) = (turn |-> king) & 
                #(ntx, nty, ncx, ncy).(
                    ntx:1..8 & nty:1..8 & ncx:1..8 & ncy:1..8 &
                    mkPair(ntx, nty) : playableBoard &
                    (mkPair(ntx, nty) /: dom(board) & // or (ntx = fromX & nty = fromY) or (ntx = capX & nty = capY)) &
                    absDiff(toX, ntx) = absDiff(toY, nty) &
                    
                    min({toX, ntx}) < ncx & ncx < max({toX, ntx}) &
                    min({toY, nty}) < ncy & ncy < max({toY, nty}) &
                    absDiff(toX, ncx) = absDiff(toY, ncy) &
                    mkPair(ncx, ncy) : dom(board) & 
                    board(mkPair(ncx, ncy)) : {opponent(turn)} * TYPE &
                    
                    not(ncx = capX & ncy = capY) & // Não pode ser a peça recém capturada
                    
                    // Checa se o caminho da dama está livre
                    !(px, py).(
                        px:1..8 & py:1..8 & 
                        min({toX, ntx}) < px & px < max({toX, ntx}) & 
                        min({toY, nty}) < py & py < max({toY, nty}) &
                        absDiff(toX, px) = absDiff(toY, py) &
                        not(px = ncx & py = ncy)
                        => 
                        (mkPair(px, py) /: dom(board) or (px = fromX & py = fromY) or (px = capX & py = capY)) // Toda posição entre a nova origem e 
                        // uma possível próxima captura está vazia ou é a origem e capturas atuais
                    )
                )
            ))
        THEN
            // Nenhuma das opções do THEN acima devem finalizar o jogo, pois há peças pra participar do combo
            SELECT board(mkPair(fromX, fromY)) = (turn |-> man) & ((turn = white & toX = 8) or (turn = black & toX = 1)) THEN // Só é possível escolher parar o combo quando há uma promoção no meio
                // Promove para dama e encerra
                turn := opponent(turn)
                || comboPiece := {}
                || board := ({mkPair(fromX, fromY), mkPair(capX, capY)} <<| board) \/ {mkPair(toX, toY) |-> (turn |-> king)}
            WHEN 1 = 1 THEN // Sempre é possível continuar o combo
                // Desiste de virar dama e continua o combo
                comboPiece := {mkPair(toX, toY)} // Tranca o turno na peça, negando virar dama para continuar o combo
                || board := ({mkPair(fromX, fromY), mkPair(capX, capY)} <<| board) \/ {mkPair(toX, toY) |-> board(mkPair(fromX, fromY))}
            END
        ELSE
            // As capturas que acontecem nessas condições podem finalizar o jogo
            turn := opponent(turn) // Passa a vez e limpa a trava
            || comboPiece := {}
            || board := ({mkPair(fromX, fromY), mkPair(capX, capY)} <<| board) \/ {mkPair(toX, toY) |-> board(mkPair(fromX, fromY))}
            || IF card(board |> ({opponent(turn)} * TYPE)) - 1 = 0 THEN // Se após realizar essa operação o oponente fica sem peças
                   gameStatus := turnToWon(turn)
               ELSIF card(board |> ({turn} * TYPE)) = 1 & card(board |> ({opponent(turn)} * TYPE)) - 1 = 1 THEN // Após realizar essa operação ambos os jogadores ficam com 1 peça
                   gameStatus := draw // A situação acima descreve um empate (supondo que ambas as partes não entreguem o jogo)
               END
        END
    END;

    
    current_status <-- checkStatus=
    BEGIN
        current_status := gameStatus
    END;
    
    reset =
    BEGIN board := 
        (whiteInit * {(white |-> man)}) \/ 
        (blackInit * {(black |-> man)})
        ||
        turn::PLAYER
        ||
        gameStatus := playing
        ||
        comboPiece := {}
    END
    
END
