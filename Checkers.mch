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
    absDiff
    
PROPERTIES
    playableBoard = {xx,yy | xx:1..8 & yy:1..8 & (xx+yy) mod 2 = 0} &
    whiteInit = {xx,yy | xx:1..3 & yy:1..8 & (xx+yy) mod 2 = 0} &
    blackInit = {xx,yy | xx:6..8 & yy:1..8 & (xx+yy) mod 2 = 0} &
    mkPair = %(xx,yy) . (xx:INTEGER & yy:INTEGER|xx |-> yy) &
    absDiff = %(nn, mm) . (nn:INTEGER & mm:INTEGER | max({nn - mm, mm - nn}))
    
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
    turn::PLAYER
    ||
    gameStatus := playing
    
OPERATIONS
    
    move(fromX, fromY, toX, toY) =
    PRE
        fromX:1..8 & fromY:1..8 & toX:1..8 & toY:1..8 &
        
        mkPair(fromX, fromY) : dom(board) &
        mkPair(toX, toY) : playableBoard &
        mkPair(toX, toY) /: dom(board) & // Não há peça na casa de destino
        
        board(mkPair(fromX, fromY)) : {turn} * TYPE & // Peça a ser movida pertence ao jogador do turno atual
        
        (
            /* Movimentação é peça normal */
            (
                board(mkPair(fromX, fromY)) = (turn |-> man) &
                
                // Movimentação diagonal
                absDiff(fromX, toX) = 1 &
                absDiff(fromY, toY) = 1 &
                
                /* checa se é um movimento de uma casa */
                ((turn = white & toX = fromX + 1) or (turn = black & toX = fromX - 1))
            )
            
            or
            
            /* Movimentação é peça coroada (dama)*/
            (
                board(mkPair(fromX,fromY)) = (turn |-> king) &
                
                absDiff(fromX, toX) = absDiff(fromY, toY) & // Movimentação apenas nas diagonais da posição atual
                
                /* checa se o caminho está livre */
                !(pathX, pathY).(
                    pathX:1..8 & pathY:1..8 &
                    
                    min({fromX, toX}) < pathX &
                    pathX < max({fromX, toX}) &
                    
                    min({fromY, toY}) < pathY &
                    pathY < max({fromY, toY}) & // Checar as casas apenas no percurso de movimento
                    
                    max({fromX - pathX, pathX - fromX}) = max({fromY - pathY, pathY - fromY}) & 
                    
                    (pathX |-> pathY) : playableBoard
                    =>
                    (pathX |-> pathY) /: dom(board) // Todas as casas entre a posição e o destino estão vazias
                )
            )
        )
        
    THEN
        
        /* promoção */
        IF board(mkPair(fromX, fromY)) = (turn |-> man) &
            ((turn = white & toX = 8) or (turn = black & toX = 1))
        THEN
            board :=
            (board - ({mkPair(fromX, fromY)} <| board)) \/
            {mkPair(toX, toY) |-> (turn |-> king)}
        ELSE
            board :=
            (board - ({mkPair(fromX, fromY)} <| board)) \/
            {mkPair(toX, toY) |-> board(mkPair(fromX, fromY))}
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