MACHINE Checkers

SEES Checkers_ctx

DEFINITIONS
    MK_PAIR(fst, snd) == (fst |-> snd);

    ABS_DIFF(nn, mm) == max({nn - mm, mm - nn});

    // Checa se a peça está no tabuleiro
    IS_ON_BOARD(posX, posY) == (posX: MIN_COORD..MAX_COORD & posY: MIN_COORD..MAX_COORD);

    // Checa se a peça está numa casa preta
    IS_BLACK_SQUARE(posX, posY) == ((posX + posY) mod 2 = 0);

    // Conjunto de casas na diagonal entre duas coordenadas 
    DIAGONAL_PATH(startX, startY, endX, endY) == {pathX, pathY |
        pathX: INTEGER &
        pathY: INTEGER &
        IS_ON_BOARD(pathX, pathY) &
        min({startX, endX}) < pathX &
        pathX < max({startX, endX}) &
        min({startY, endY}) < pathY &
        pathY < max({startY, endY}) &
        ABS_DIFF(startX, pathX) = ABS_DIFF(startY, pathY)
    };

    // Movimentos válidos no tabuleiro 
    NORMAL_MOVES(bState, player) == {nfX, nfY, ntX, ntY |
        nfX: INTEGER &
        nfY: INTEGER &
        ntX: INTEGER &
        ntY: INTEGER &
        IS_ON_BOARD(nfX, nfY) &
        IS_ON_BOARD(ntX, ntY) &
        MK_PAIR(nfX, nfY) : dom(bState) &
        bState(MK_PAIR(nfX, nfY)) : {player} * TYPE &
        IS_BLACK_SQUARE(ntX, ntY) &
        MK_PAIR(ntX, ntY) /: dom(bState) &
        (
            // Regra do Peão
            (
                bState(MK_PAIR(nfX, nfY)) = (player |-> man) &
                ABS_DIFF(nfX, ntX) = 1 &
                ABS_DIFF(nfY, ntY) = 1 &
                ((player = white & ntX = nfX + 1) or (player = black & ntX = nfX - 1))
            )
            or
            // Regra da Dama
            (
                bState(MK_PAIR(nfX, nfY)) = (player |-> king) &
                ABS_DIFF(nfX, ntX) = ABS_DIFF(nfY, ntY) &
                DIAGONAL_PATH(nfX, nfY, ntX, ntY) /\ dom(bState) = {} // Caminho vazio
            )
        )
    };

    // Capturas válidas no tabuleiro 
    CAPTURE_MOVES(bState, player) == {cfX, cfY, ctX, ctY |
        cfX: INTEGER &
        cfY: INTEGER &
        ctX: INTEGER &
        ctY: INTEGER &
        IS_ON_BOARD(cfX, cfY) &
        IS_ON_BOARD(ctX, ctY) &
        MK_PAIR(cfX, cfY) : dom(bState) &
        bState(MK_PAIR(cfX, cfY)) : {player} * TYPE &
        IS_BLACK_SQUARE(ctX, ctY) &
        MK_PAIR(ctX, ctY) /: dom(bState) &
        (
            // Regra de Captura do Peão
            (
                bState(MK_PAIR(cfX, cfY)) = (player |-> man) &
                ABS_DIFF(cfX, ctX) = 2 &
                ABS_DIFF(cfY, ctY) = 2 &
                {capX, capY |
                    capX: INTEGER &
                    capY: INTEGER &
                    IS_ON_BOARD(capX, capY) &
                    IS_BLACK_SQUARE(capX, capY) &
                    capX * 2 = cfX + ctX &
                    capY * 2 = cfY + ctY
                } /\ dom(bState |> ({opponent(player)} * TYPE)) /= {}
            )
            or
            // Regra de Captura da Dama
            (
                bState(MK_PAIR(cfX, cfY)) = (player |-> king) &
                ABS_DIFF(cfX, ctX) = ABS_DIFF(cfY, ctY) &
                card(DIAGONAL_PATH(cfX, cfY, ctX, ctY) /\ dom(bState |> ({opponent(player)} * TYPE))) = 1 & // Exatamente 1 inimigo no caminho
                DIAGONAL_PATH(cfX, cfY, ctX, ctY) /\ dom(bState |> ({player} * TYPE)) = {} // Nenhum "aliado" no caminho
            )
        )
    };

    // Checa se o jogador tem alguma jogada possível 
    HAS_AVAILABLE_MOVES_ON(bState, player) == (NORMAL_MOVES(bState, player) \/ CAPTURE_MOVES(bState, player) /= {});

    // Checa se uma peça específica pode continuar capturando no novo estado do tabuleiro
    HAS_CONTINUOUS_CAPTURE(bState, player, startX, startY) ==
        ({contX, contY |
            contX: INTEGER &
            contY: INTEGER &
            IS_ON_BOARD(contX, contY) &
            IS_BLACK_SQUARE(contX, contY) &
            startX |-> startY |-> contX |-> contY : CAPTURE_MOVES(bState, player)
        } /= {});

    PLAYABLE_BOARD == {posX, posY |
        posX: MIN_COORD..MAX_COORD &
        posY: MIN_COORD..MAX_COORD &
        IS_BLACK_SQUARE(posX, posY)
    };

    WHITE_INIT == {posX, posY |
        posX: MIN_COORD..3 &
        posY: MIN_COORD..MAX_COORD &
        IS_BLACK_SQUARE(posX, posY)
    };

    BLACK_INIT == {posX, posY |
        posX: 6..MAX_COORD &
        posY: MIN_COORD..MAX_COORD &
        IS_BLACK_SQUARE(posX, posY)
    }

CONSTANTS
    opponent,
    turnToWon

PROPERTIES
    opponent = {white |-> black, black |-> white} &
    turnToWon = {white |-> whiteWon, black |-> blackWon}

VARIABLES
    board,
    turn,
    gameStatus,
    comboPiece,
    lastMoveWas,
    opponentCouldCaptureWith

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

    // Uma peça jamais sairá do tabuleiro 
    !(posX, posY).(posX: INTEGER & posY: INTEGER & MK_PAIR(posX, posY) : dom(board) => IS_ON_BOARD(posX, posY)) &

    // Uma peça jamais estará em uma casa branca
    !(posX, posY).(posX: INTEGER & posY: INTEGER & MK_PAIR(posX, posY) : dom(board) => IS_BLACK_SQUARE(posX, posY)) &

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
    board :=
        (WHITE_INIT * {(white |-> man)}) \/
        (BLACK_INIT * {(black |-> man)})
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
        IF board(MK_PAIR(fromX, fromY)) = (turn |-> man) & ((turn = white & toX = MAX_COORD) or (turn = black & toX = MIN_COORD)) THEN
            LET nextBoard BE nextBoard = ({MK_PAIR(fromX, fromY)} <<| board) \/ {MK_PAIR(toX, toY) |-> (turn |-> king)} IN // Promoção
                board := nextBoard ||
                IF HAS_AVAILABLE_MOVES_ON(nextBoard, opponent(turn)) THEN
                    turn := opponent(turn)
                ELSE
                    gameStatus := turnToWon(turn)
                END
            END
        ELSE
            LET nextBoard BE nextBoard = ({MK_PAIR(fromX, fromY)} <<| board) \/ {MK_PAIR(toX, toY) |-> board(MK_PAIR(fromX, fromY))} IN // Movimento normal
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
               IF MK_PAIR(fromX, fromY) : moves // A peça sendo movida é uma das que poderia capturar
               THEN opponentCouldCaptureWith := (moves - {MK_PAIR(fromX, fromY)}) \/ {MK_PAIR(toX, toY)} // Logo deve ser atualizada para a nova posição no conjunto de peças passíveis de sopro
               ELSE opponentCouldCaptureWith := moves
               END
           END
    END;

    capture(fromX, fromY, toX, toY, capX, capY) =
    PRE
        fromX: INTEGER & fromY: INTEGER & toX: INTEGER & toY: INTEGER & capX: INTEGER & capY: INTEGER &
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
            (board(MK_PAIR(fromX, fromY)) = (turn |-> king) & MK_PAIR(capX, capY) : DIAGONAL_PATH(fromX, fromY, toX, toY) /\ dom(board |> ({opponent(turn)} * TYPE)))  // Captura está entre a origem e destino e a casa pertence ao oponente
        )
    THEN
        LET nextBoard BE nextBoard = ({MK_PAIR(fromX, fromY), MK_PAIR(capX, capY)} <<| board) \/ {MK_PAIR(toX, toY) |-> board(MK_PAIR(fromX, fromY))} IN
            // Checa no "futuro" tabuleiro se a mesma peça tem mais capturas
            IF HAS_CONTINUOUS_CAPTURE(nextBoard, turn, toX, toY) THEN

                // Nenhuma das opções do THEN acima devem finalizar o jogo, pois há peças pra participar do combo
                SELECT board(MK_PAIR(fromX, fromY)) = (turn |-> man) & ((turn = white & toX = MAX_COORD) or (turn = black & toX = MIN_COORD)) THEN // Só é possível escolher parar o combo quando há uma promoção no meio
                    turn := opponent(turn)
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
        MK_PAIR(xx, yy) : dom(board) &
        board(MK_PAIR(xx, yy)) : {opponent(turn)} * TYPE &
        MK_PAIR(xx, yy) : opponentCouldCaptureWith &
        lastMoveWas = moved // Só permitir pedir sopro quando o último movimento tiver sido um movimento
    THEN
        LET nextBoard BE nextBoard = {MK_PAIR(xx, yy)} <<| board IN
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
        MK_PAIR(fromX, fromY) : dom(board) & // Pertencer ao tabuleiro garante estar numa casa escura
        board(MK_PAIR(fromX, fromY)) : {turn} * TYPE
    THEN
        ANY moves WHERE
            moves = {destX, destY |
                destX: INTEGER &
                destY: INTEGER &
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
    BEGIN
        board :=
            (WHITE_INIT * {(white |-> man)}) \/
            (BLACK_INIT * {(black |-> man)})
        || turn :: PLAYER
        || gameStatus := playing
        || comboPiece := {}
        || lastMoveWas := idle
        || opponentCouldCaptureWith := {}
    END

END
