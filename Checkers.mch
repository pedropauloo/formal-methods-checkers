MACHINE Checkers
    
DEFINITIONS "checkers_defs.def"

SETS
    PLAYER = {white, black};
    TYPE = {man, king};
    STATUS = {playing, whiteWon, blackWon, draw};
    MOVE = {idle, moved, captured, huffed}
    
CONSTANTS
    MIN_COORD,
    MAX_COORD,
    MAX_MOVES,
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
    MIN_COORD = 1 &
    MAX_COORD = 8 &
    MAX_MOVES = 32 &
    playableBoard = {posX, posY | posX:MIN_COORD..MAX_COORD & posY:MIN_COORD..MAX_COORD & IS_BLACK_SQUARE(posX, posY)} &
    whiteInit = {posX, posY | posX:MIN_COORD..3 & posY:MIN_COORD..MAX_COORD & IS_BLACK_SQUARE(posX, posY)} &
    blackInit = {posX, posY | posX:6..MAX_COORD & posY:MIN_COORD..MAX_COORD & IS_BLACK_SQUARE(posX, posY)} &
    mkPair = %(posX, posY) . (posX:INTEGER & posY:INTEGER | posX |-> posY) &
    absDiff = %(nn, mm) . (nn:INTEGER & mm:INTEGER | max({nn - mm, mm - nn})) &
    opponent = {white |-> black, black |-> white} &
    turnToWon = {white |-> whiteWon, black |-> blackWon} &

    captureBoard = { // Testes de captura e de sopro
        (1 |-> 1) |-> (white |-> man),
        (3 |-> 3) |-> (black |-> man),
        (4 |-> 4) |-> (white |-> man),
        (4 |-> 6) |-> (white |-> man),
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
    comboPiece,
    lastMoveWas,
    opponentCouldCaptureWith
    
INVARIANT
    board : playableBoard +-> (PLAYER * TYPE) &
    turn : PLAYER &
    gameStatus : STATUS &
    comboPiece <: playableBoard &
    comboPiece : FIN(comboPiece) &
    card(comboPiece) <= 1 &
    lastMoveWas : MOVE &
    opponentCouldCaptureWith <: playableBoard &
    opponentCouldCaptureWith : FIN(opponentCouldCaptureWith) &
    
    // Uma peça jamais sairá do tabuleiro 
    !(posX, posY).(posX: INTEGER & posY: INTEGER & mkPair(posX, posY) : dom(board) => IS_ON_BOARD(posX, posY)) &
    
    // Uma peça jamais estará em uma casa branca
    !(posX, posY).(posX: INTEGER & posY: INTEGER & mkPair(posX, posY) : dom(board) => IS_BLACK_SQUARE(posX, posY)) &

    // Talvez juntar as duas cláusulas acima seja mais otimizado?

    (
        (gameStatus = playing & card(board |> ({white} * TYPE)) > 0 & card(board |> ({black} * TYPE)) > 0) 
        or
        ((gameStatus = whiteWon & card(board |> ({black} * TYPE)) = 0) or (gameStatus = blackWon & card(board |> ({white} * TYPE)) = 0))
        or
        (gameStatus = draw & card(board |> ({black} * TYPE)) = 1 & card(board |> ({white} * TYPE)) = 1)
        or
        // Permite status de vitória caso o oponente tenha peças, mas não tenha movimentos
        (gameStatus = whiteWon & card(board |> ({black} * TYPE)) > 0 & not(HAS_AVAILABLE_MOVES_ON(board, black)))
        or
        (gameStatus = blackWon & card(board |> ({white} * TYPE)) > 0 & not(HAS_AVAILABLE_MOVES_ON(board, white)))
    )
    
INITIALISATION
    CHOICE board:=
        (whiteInit * {(white |-> man)}) \/ 
        (blackInit * {(black |-> man)})
        OR board := captureBoard
        OR board := drawBoard
        OR board := victoryBoard
    END
    || turn::PLAYER // Permite que qualquer jogador comece o jogo
    || gameStatus := playing
    || comboPiece := {}
    || lastMoveWas := idle
    || opponentCouldCaptureWith := {}
    
OPERATIONS
    
    move(fromX, fromY, toX, toY) =
    PRE
        fromX: INTEGER & fromY: INTEGER & toX: INTEGER & toY: INTEGER &
        gameStatus = playing &
        comboPiece = {} & // Não pode fazer movimento normal no meio de um combo
        
        // Checa se há capturas a serem feitas
        // Caso exista movimento de captura, é obrigatório escolher entre um deles
        // CAPTURE_MOVES(board, turn) = {} & // Retirado para implementar a possibilidade de sopro
        
        // O movimento deve pertencer ao conjunto de movimentos válidos
        fromX |-> fromY |-> toX |-> toY : NORMAL_MOVES(board, turn)
    THEN
        IF board(mkPair(fromX, fromY)) = (turn |-> man) & ((turn = white & toX = MAX_COORD) or (turn = black & toX = MIN_COORD)) THEN
            LET nextBoard BE nextBoard = ({mkPair(fromX, fromY)} <<| board) \/ {mkPair(toX, toY) |-> (turn |-> king)} IN // Promoção
                board := nextBoard ||
                IF HAS_AVAILABLE_MOVES_ON(nextBoard, opponent(turn)) THEN
                    turn := opponent(turn)
                ELSE
                    gameStatus := turnToWon(turn)
                END
            END
        ELSE
            LET nextBoard BE nextBoard = ({mkPair(fromX, fromY)} <<| board) \/ {mkPair(toX, toY) |-> board(mkPair(fromX, fromY))} IN // Movimento normal
                board := nextBoard ||
                IF HAS_AVAILABLE_MOVES_ON(nextBoard, opponent(turn)) THEN
                    turn := opponent(turn)
                ELSE
                    gameStatus := turnToWon(turn)
                END
            END
        END
        || lastMoveWas := moved
        || LET moves BE moves = dom(dom(CAPTURE_MOVES(board, turn))) IN // Resultado de CAPTURE_MOVES é considerado uma função (INT -> INT -> INT) -> INT
               IF mkPair(fromX, fromY) : moves // A peça sendo movida é uma das que poderia capturar
               THEN opponentCouldCaptureWith := (moves - {mkPair(fromX, fromY)}) \/ {mkPair(toX, toY)} // Logo deve ser atualizada para a nova posição no conjunto de peças passíveis de sopro
               ELSE opponentCouldCaptureWith :=  moves
               END
           END
    END;
    
    capture(fromX, fromY, toX, toY, capX, capY) =
    PRE
        fromX: INTEGER & fromY: INTEGER & toX: INTEGER & toY: INTEGER & capX: INTEGER & capY: INTEGER & 
        gameStatus = playing &
        mkPair(capX, capY) : dom(board) &
        
        // O movimento de captura deve ser um movimento válido
        fromX |-> fromY |-> toX |-> toY : CAPTURE_MOVES(board, turn) &
        
        // Se a captura é múltipla, a origem atual é obrigatoriamente o destino da anterior
        (comboPiece /= {} => mkPair(fromX, fromY) : comboPiece) &
        
        // Garante que 'capX' e 'capY' apontam de fato para a peça correta
        (
            (board(mkPair(fromX, fromY)) = (turn |-> man) & capX * 2 = fromX + toX & capY * 2 = fromY + toY) // Posição de captura é o ponto médio entre a origem e o destino
            or
            (board(mkPair(fromX, fromY)) = (turn |-> king) & mkPair(capX, capY) : DIAGONAL_PATH(fromX, fromY, toX, toY) /\ dom(board |> ({opponent(turn)} * TYPE)))  // Captura está entre a origem e destino e a casa pertence ao oponente
        )
    THEN
        LET nextBoard BE nextBoard = ({mkPair(fromX, fromY), mkPair(capX, capY)} <<| board) \/ {mkPair(toX, toY) |-> board(mkPair(fromX, fromY))} IN
            // Checa no "futuro" tabuleiro se a mesma peça tem mais capturas
            IF HAS_CONTINUOUS_CAPTURE(nextBoard, turn, toX, toY) THEN
                
                // Nenhuma das opções do THEN acima devem finalizar o jogo, pois há peças pra participar do combo
                SELECT board(mkPair(fromX, fromY)) = (turn |-> man) & ((turn = white & toX = MAX_COORD) or (turn = black & toX = MIN_COORD)) THEN // Só é possível escolher parar o combo quando há uma promoção no meio
                    turn := opponent(turn)
                    || comboPiece := {}
                    || board := ({mkPair(toX, toY)} <<| nextBoard) \/ {mkPair(toX, toY) |-> (turn |-> king)}
                WHEN 1 = 1 THEN  // Sempre é possível continuar o combo
                    // Desiste de virar dama e continua o combo
                    comboPiece := {mkPair(toX, toY)} // Tranca o turno na peça, negando virar dama para continuar o combo
                    || board := nextBoard
                END
                
            ELSE
                // As capturas que acontecem nessas condições podem finalizar o jogo
                board := nextBoard
                || turn := opponent(turn)  // Passa a vez e limpa a trava
                || comboPiece := {}
                || IF card(nextBoard |> ({opponent(turn)} * TYPE)) = 0 THEN
                       gameStatus := turnToWon(turn) // Perdeu por falta de peças
                   ELSIF not(HAS_AVAILABLE_MOVES_ON(nextBoard, opponent(turn))) THEN
                       gameStatus := turnToWon(turn) // Perdeu por falta de movimentos
                   END
            END
        END
        || lastMoveWas := captured
        || opponentCouldCaptureWith := {} // dom(dom(CAPTURE_MOVES(board, turn))) // Deixar {} para otimizar?
    END;

    // Operação de sopro
    huff(xx, yy) =
    PRE
        xx : INTEGER & yy : INTEGER &
        gameStatus = playing &
        mkPair(xx, yy) : dom(board) &
        board(mkPair(xx, yy)) : {opponent(turn)} * TYPE &
        mkPair(xx, yy) : opponentCouldCaptureWith &
        lastMoveWas = moved // Só permitir pedir sopro quando o último movimento tiver sido um movimento
    THEN
        LET nextBoard BE nextBoard = {mkPair(xx, yy)} <<| board IN
            board := nextBoard
            || IF card(nextBoard |> ({opponent(turn)} * TYPE)) = 0 THEN
                   gameStatus := turnToWon(turn) // Perdeu por falta de peças
               ELSIF not(HAS_AVAILABLE_MOVES_ON(nextBoard, opponent(turn))) THEN
                   gameStatus := turnToWon(turn) // Perdeu por falta de movimentos
               END
        END
        || lastMoveWas := huffed
    END;

    // Retorna TODAS as posições válidas de movimento para uma dada peça
    validMoves, moveCount <-- getPossibleMoves(fromX, fromY) =
    PRE
        fromX: INTEGER & fromY: INTEGER & 
        IS_ON_BOARD(fromX, fromY) &
        mkPair(fromX, fromY) : dom(board) & // Pertencer ao tabuleiro garante estar numa casa escura
        board(mkPair(fromX, fromY)) : {turn} * TYPE
    THEN
        ANY moves WHERE
            moves = { destX, destY | 
                destX: INTEGER & destY: INTEGER &
                fromX |-> fromY |-> destX |-> destY : NORMAL_MOVES(board, turn) \/ CAPTURE_MOVES(board, turn)
            } &
            moves <: playableBoard &
            card(moves) <= MAX_MOVES
        THEN
            moveCount := card(moves)
            ||
            validMoves :: 1..card(moves) >->> moves
        END
    END;
    
    currentStatus <-- checkStatus =
    BEGIN
        currentStatus := gameStatus
    END;
    
    reset =
    BEGIN board := 
        (whiteInit * {(white |-> man)}) \/ 
        (blackInit * {(black |-> man)})
        || turn::PLAYER
        || gameStatus := playing
        || comboPiece := {}
    END
    
END
