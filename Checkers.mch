MACHINE Checkers
    
DEFINITIONS "checkers_defs.def"

SEES Checkers_ctx

VARIABLES
    board,
    turn,
    gameStatus,
    comboPiece,
    lastMoveWas,
    opponentCouldCaptureWith,
    getPlayer,
    opponent,
    turnToWon
    
INVARIANT
    board : PLAYABLE_BOARD +-> (PLAYER * TYPE) &
    turn : PLAYER &
    gameStatus : STATUS &
    comboPiece <: PLAYABLE_BOARD &
    comboPiece : FIN(comboPiece) &
    card(comboPiece) <= 1 &
    lastMoveWas : MOVE &
    opponentCouldCaptureWith <: PLAYABLE_BOARD &
    opponentCouldCaptureWith : FIN(opponentCouldCaptureWith) &
    getPlayer : PLAYER --> 0..1 &
    opponent : 0..1 --> PLAYER &
    turnToWon : 0..1 --> STATUS &
    
    // Uma peça jamais sairá do tabuleiro 
    !(posX, posY).(posX: INT & posY: INT & MK_PAIR(posX, posY) : dom(board) => IS_ON_BOARD(posX, posY)) &
    
    // Uma peça jamais estará em uma casa branca
    !(posX, posY).(posX: INT & posY: INT & MK_PAIR(posX, posY) : dom(board) => IS_BLACK_SQUARE(posX, posY)) &

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
    board:=
        (WHITE_INIT * {(white |-> man)}) \/ 
        (BLACK_INIT * {(black |-> man)})
    || turn::PLAYER // Permite que qualquer jogador comece o jogo
    || gameStatus := playing
    || comboPiece := {}
    || lastMoveWas := idle
    || opponentCouldCaptureWith := {}
    || getPlayer := %pp.(pp : PLAYER & pp = white | 0) \/ %pp.(pp : PLAYER & pp = black | 1)
    || opponent := %nn.(nn : 0..1 & nn = 0 | black) \/ %nn.(nn : 0..1 & nn = 1 | white)
    || turnToWon := %nn.(nn: 0..1 & nn = 0 | whiteWon) \/ %nn.(nn : 0..1 & nn = 1 | blackWon)
    
OPERATIONS
    
    move(fromX, fromY, toX, toY) =
    PRE
        fromX: INT & fromY: INT & toX: INT & toY: INT &
        gameStatus = playing &
        comboPiece = {} & // Não pode fazer movimento normal no meio de um combo
        
        // Checa se há capturas a serem feitas
        // Caso exista movimento de captura, é obrigatório escolher entre um deles
        // CAPTURE_MOVES(board, turn) = {} & // Retirado para implementar a possibilidade de sopro
        
        // O movimento deve pertencer ao conjunto de movimentos válidos
        fromX |-> fromY |-> toX |-> toY : NORMAL_MOVES(board, turn)
    THEN
        IF board(MK_PAIR(fromX, fromY)) = (turn |-> man) & ((turn = white & toX = MAX_COORD) or (turn = black & toX = MIN_COORD)) THEN
            LET nextBoard BE nextBoard = ({MK_PAIR(fromX, fromY)} <<| board) \/ {MK_PAIR(toX, toY) |-> (turn |-> king)} IN // Promoção
                board := nextBoard ||
                IF HAS_AVAILABLE_MOVES_ON(nextBoard, opponent(getPlayer(turn))) THEN
                    turn := opponent(getPlayer(turn))
                ELSE
                    gameStatus := turnToWon(getPlayer(turn))
                END
            END
        ELSE
            LET nextBoard BE nextBoard = ({MK_PAIR(fromX, fromY)} <<| board) \/ {MK_PAIR(toX, toY) |-> board(MK_PAIR(fromX, fromY))} IN // Movimento normal
                board := nextBoard ||
                IF HAS_AVAILABLE_MOVES_ON(nextBoard, opponent(getPlayer(turn))) THEN
                    turn := opponent(getPlayer(turn))
                ELSE
                    gameStatus := turnToWon(getPlayer(turn))
                END
            END
        END
        || lastMoveWas := moved
        || LET moves BE moves = dom(dom(CAPTURE_MOVES(board, turn))) IN // Resultado de CAPTURE_MOVES é considerado uma função (INT -> INT -> INT) -> INT
               IF MK_PAIR(fromX, fromY) : moves // A peça sendo movida é uma das que poderia capturar
               THEN opponentCouldCaptureWith := (moves - {MK_PAIR(fromX, fromY)}) \/ {MK_PAIR(toX, toY)} // Logo deve ser atualizada para a nova posição no conjunto de peças passíveis de sopro
               ELSE opponentCouldCaptureWith :=  moves
               END
           END
    END;
    
    capture(fromX, fromY, toX, toY, capX, capY) =
    PRE
        fromX: INT & fromY: INT & toX: INT & toY: INT & capX: INT & capY: INT & 
        gameStatus = playing &
        MK_PAIR(capX, capY) : dom(board) &
        
        // O movimento de captura deve ser um movimento válido
        fromX |-> fromY |-> toX |-> toY : CAPTURE_MOVES(board, turn) &
        
        // Se a captura é múltipla, a origem atual é obrigatoriamente o destino da anterior
        (comboPiece /= {} => MK_PAIR(fromX, fromY) : comboPiece) &
        
        // Garante que 'capX' e 'capY' apontam de fato para a peça correta
        (
            (board(MK_PAIR(fromX, fromY)) = (turn |-> man) & capX * 2 = fromX + toX & capY * 2 = fromY + toY) // Posição de captura é o ponto médio entre a origem e o destino
            or
            (board(MK_PAIR(fromX, fromY)) = (turn |-> king) & MK_PAIR(capX, capY) : DIAGONAL_PATH(fromX, fromY, toX, toY) /\ dom(board |> ({opponent(getPlayer(turn))} * TYPE)))  // Captura está entre a origem e destino e a casa pertence ao oponente
        )
    THEN
        LET nextBoard BE nextBoard = ({MK_PAIR(fromX, fromY), MK_PAIR(capX, capY)} <<| board) \/ {MK_PAIR(toX, toY) |-> board(MK_PAIR(fromX, fromY))} IN
            // Checa no "futuro" tabuleiro se a mesma peça tem mais capturas
            IF HAS_CONTINUOUS_CAPTURE(nextBoard, turn, toX, toY) THEN
                
                // Nenhuma das opções do THEN acima devem finalizar o jogo, pois há peças pra participar do combo
                SELECT board(MK_PAIR(fromX, fromY)) = (turn |-> man) & ((turn = white & toX = MAX_COORD) or (turn = black & toX = MIN_COORD)) THEN // Só é possível escolher parar o combo quando há uma promoção no meio
                    turn := opponent(getPlayer(turn))
                    || comboPiece := {}
                    || board := ({MK_PAIR(toX, toY)} <<| nextBoard) \/ {MK_PAIR(toX, toY) |-> (turn |-> king)}
                WHEN 1 = 1 THEN  // Sempre é possível continuar o combo
                    // Desiste de virar dama e continua o combo
                    comboPiece := {MK_PAIR(toX, toY)} // Tranca o turno na peça, negando virar dama para continuar o combo
                    || board := nextBoard
                END
                
            ELSE
                // As capturas que acontecem nessas condições podem finalizar o jogo
                board := nextBoard
                || turn := opponent(getPlayer(turn))  // Passa a vez e limpa a trava
                || comboPiece := {}
                || IF card(nextBoard |> ({opponent(getPlayer(turn))} * TYPE)) = 0 THEN
                       gameStatus := turnToWon(getPlayer(turn)) // Perdeu por falta de peças
                   ELSIF not(HAS_AVAILABLE_MOVES_ON(nextBoard, opponent(getPlayer(turn)))) THEN
                       gameStatus := turnToWon(getPlayer(turn)) // Perdeu por falta de movimentos
                   END
            END
        END
        || lastMoveWas := captured
        || opponentCouldCaptureWith := {} // dom(dom(CAPTURE_MOVES(board, turn))) // Deixar {} para otimizar?
    END;

    // Operação de sopro
    huff(xx, yy) =
    PRE
        xx : INT & yy : INT &
        gameStatus = playing &
        MK_PAIR(xx, yy) : dom(board) &
        board(MK_PAIR(xx, yy)) : {opponent(getPlayer(turn))} * TYPE &
        MK_PAIR(xx, yy) : opponentCouldCaptureWith &
        lastMoveWas = moved // Só permitir pedir sopro quando o último movimento tiver sido um movimento
    THEN
        LET nextBoard BE nextBoard = {MK_PAIR(xx, yy)} <<| board IN
            board := nextBoard
            || IF card(nextBoard |> ({opponent(getPlayer(turn))} * TYPE)) = 0 THEN
                   gameStatus := turnToWon(getPlayer(turn)) // Perdeu por falta de peças
               ELSIF not(HAS_AVAILABLE_MOVES_ON(nextBoard, opponent(getPlayer(turn)))) THEN
                   gameStatus := turnToWon(getPlayer(turn)) // Perdeu por falta de movimentos
               END
        END
        || lastMoveWas := huffed
    END;

    // Retorna TODAS as posições válidas de movimento para uma dada peça
    validMoves, moveCount <-- getPossibleMoves(fromX, fromY) =
    PRE
        fromX: INT & fromY: INT & 
        IS_ON_BOARD(fromX, fromY) &
        MK_PAIR(fromX, fromY) : dom(board) & // Pertencer ao tabuleiro garante estar numa casa escura
        board(MK_PAIR(fromX, fromY)) : {turn} * TYPE
    THEN
        ANY moves WHERE
            moves = { destX, destY | 
                destX: INT & destY: INT &
                fromX |-> fromY |-> destX |-> destY : NORMAL_MOVES(board, turn) \/ CAPTURE_MOVES(board, turn)
            } &
            moves <: PLAYABLE_BOARD &
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
        (WHITE_INIT * {(white |-> man)}) \/ 
        (BLACK_INIT * {(black |-> man)})
        || turn::PLAYER
        || gameStatus := playing
        || comboPiece := {}
    END
    
END
