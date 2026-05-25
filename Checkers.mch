MACHINE Checkers
    
DEFINITIONS
    // Checa se a peça está no tabuleiro
    IS_ON_BOARD(posX, posY) == (posX: MIN_COORD..MAX_COORD & posY: MIN_COORD..MAX_COORD);
    // Checa se a peça está numa casa preta
    IS_BLACK_SQUARE(posX, posY) == ((posX+posY) mod 2 = 0);
    
    // Conjunto de casas na diagonal entre duas coordenadas 
    DIAGONAL_PATH(startX, startY, endX, endY) == { pathX, pathY | 
        pathX: INTEGER & pathY: INTEGER & 
        IS_ON_BOARD(pathX, pathY) & 
        min({startX, endX}) < pathX & pathX < max({startX, endX}) & 
        min({startY, endY}) < pathY & pathY < max({startY, endY}) & 
        absDiff(startX, pathX) = absDiff(startY, pathY)
    };

    // Movimentos válidos no tabuleiro 
    NORMAL_MOVES(bState, player) == { nfX, nfY, ntX, ntY |
        nfX: INTEGER & nfY: INTEGER & ntX: INTEGER & ntY: INTEGER & 
        IS_ON_BOARD(nfX, nfY) & IS_ON_BOARD(ntX, ntY) &
        mkPair(nfX, nfY) : dom(bState) & bState(mkPair(nfX, nfY)) : {player} * TYPE &
        mkPair(ntX, ntY) : playableBoard & mkPair(ntX, ntY) /: dom(bState) &
        (
            // Regra do Peão
            (bState(mkPair(nfX, nfY)) = (player |-> man) & 
             absDiff(nfX, ntX) = 1 & absDiff(nfY, ntY) = 1 & 
             ((player = white & ntX = nfX + 1) or (player = black & ntX = nfX - 1)))
            or
            // Regra da Dama
            (bState(mkPair(nfX, nfY)) = (player |-> king) & 
             absDiff(nfX, ntX) = absDiff(nfY, ntY) & 
             DIAGONAL_PATH(nfX, nfY, ntX, ntY) /\ dom(bState) = {}) // Caminho vazio
        )
    };

    // Capturas válidas no tabuleiro 
    CAPTURE_MOVES(bState, player) == { cfX, cfY, ctX, ctY |
        cfX: INTEGER & cfY: INTEGER & ctX: INTEGER & ctY: INTEGER & 
        IS_ON_BOARD(cfX, cfY) & IS_ON_BOARD(ctX, ctY) &
        mkPair(cfX, cfY) : dom(bState) & bState(mkPair(cfX, cfY)) : {player} * TYPE &
        mkPair(ctX, ctY) : playableBoard & mkPair(ctX, ctY) /: dom(bState) &
        (
            // Regra de Captura do Peão
            (bState(mkPair(cfX, cfY)) = (player |-> man) & 
             absDiff(cfX, ctX) = 2 & absDiff(cfY, ctY) = 2 &
             {capX, capY | capX: INTEGER & capY: INTEGER & IS_ON_BOARD(capX, capY) & capX * 2 = cfX + ctX & capY * 2 = cfY + ctY} /\ dom(bState |> ({opponent(player)} * TYPE)) /= {}
            )
            or
            // Regra de Captura da Dama
            (bState(mkPair(cfX, cfY)) = (player |-> king) & 
             absDiff(cfX, ctX) = absDiff(cfY, ctY) &
             card(DIAGONAL_PATH(cfX, cfY, ctX, ctY) /\ dom(bState |> ({opponent(player)} * TYPE))) = 1 & // Exatamente 1 inimigo no caminho
             DIAGONAL_PATH(cfX, cfY, ctX, ctY) /\ dom(bState |> ({player} * TYPE)) = {} // Nenhum "aliado" no caminho
            )
        )
    };

    // Checa se o jogador tem alguma jogada possível 
    HAS_AVAILABLE_MOVES_ON(bState, player) == (NORMAL_MOVES(bState, player) \/ CAPTURE_MOVES(bState, player) /= {});
    
    // Checa se uma peça específica pode continuar capturando no novo estado do tabuleiro
    HAS_CONTINUOUS_CAPTURE(bState, player, startX, startY) == 
        ({ contX, contY | contX: INTEGER & contY: INTEGER & IS_ON_BOARD(contX, contY) & startX, startY, contX, contY : CAPTURE_MOVES(bState, player) } /= {})

SETS
    PLAYER = {white, black};
    TYPE = {man, king};
    STATUS = {playing, white_won, black_won, draw}
    
CONSTANTS
    MIN_COORD,
    MAX_COORD,
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
    playableBoard = {posX, posY | posX:MIN_COORD..MAX_COORD & posY:MIN_COORD..MAX_COORD & IS_BLACK_SQUARE(posX, posY)} &
    whiteInit = {posX, posY | posX:MIN_COORD..3 & posY:MIN_COORD..MAX_COORD & IS_BLACK_SQUARE(posX, posY)} &
    blackInit = {posX, posY | posX:6..MAX_COORD & posY:MIN_COORD..MAX_COORD & IS_BLACK_SQUARE(posX, posY)} &
    mkPair = %(posX, posY) . (posX:INTEGER & posY:INTEGER | posX |-> posY) &
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
    
    // Uma peça jamais sairá do tabuleiro 
    !(posX, posY).(posX: INTEGER & posY: INTEGER & mkPair(posX, posY) : dom(board) => IS_ON_BOARD(posX, posY)) &
    
    // Uma peça jamais estará em uma casa branca
    !(posX, posY).(posX: INTEGER & posY: INTEGER & mkPair(posX, posY) : dom(board) => IS_BLACK_SQUARE(posX, posY)) &

    (
        (gameStatus = playing & card(board |> ({white} * TYPE)) > 0 & card(board |> ({black} * TYPE)) > 0) 
        or
        ((gameStatus = white_won & card(board |> ({black} * TYPE)) = 0) or (gameStatus = black_won & card(board |> ({white} * TYPE)) = 0))
        or
        (gameStatus = draw & card(board |> ({black} * TYPE)) = 1 & card(board |> ({white} * TYPE)) = 1)
        or
        // Permite status de vitória caso o oponente tenha peças, mas não tenha movimentos
        (gameStatus = white_won & card(board |> ({black} * TYPE)) > 0)
        or
        (gameStatus = black_won & card(board |> ({white} * TYPE)) > 0)
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
    
OPERATIONS
    
    move(fromX, fromY, toX, toY) =
    PRE
        fromX: INTEGER & fromY: INTEGER & toX: INTEGER & toY: INTEGER &
        gameStatus = playing &
        comboPiece = {} & // Não pode fazer movimento normal no meio de um combo
        
        // Checa se há capturas a serem feitas
        // Caso exista movimento de captura, é obrigatório escolher entre um deles
        CAPTURE_MOVES(board, turn) = {} & 
        
        // O movimento deve pertencer ao conjunto de movimentos válidos
        fromX, fromY, toX, toY : NORMAL_MOVES(board, turn)
    THEN
        IF board(mkPair(fromX, fromY)) = (turn |-> man) & ((turn = white & toX = MAX_COORD) or (turn = black & toX = MIN_COORD)) THEN
            LET next_board BE next_board = ({mkPair(fromX, fromY)} <<| board) \/ {mkPair(toX, toY) |-> (turn |-> king)} IN // Promoção
                board := next_board ||
                IF HAS_AVAILABLE_MOVES_ON(next_board, opponent(turn)) THEN
                    turn := opponent(turn)
                ELSE
                    gameStatus := turnToWon(turn)
                END
            END
        ELSE
            LET next_board BE next_board = ({mkPair(fromX, fromY)} <<| board) \/ {mkPair(toX, toY) |-> board(mkPair(fromX, fromY))} IN // Movimento normal
                board := next_board ||
                IF HAS_AVAILABLE_MOVES_ON(next_board, opponent(turn)) THEN
                    turn := opponent(turn)
                ELSE
                    gameStatus := turnToWon(turn)
                END
            END
        END
    END;
    
    capture(fromX, fromY, toX, toY, capX, capY) =
    PRE
        fromX: INTEGER & fromY: INTEGER & toX: INTEGER & toY: INTEGER & capX: INTEGER & capY: INTEGER & 
        gameStatus = playing &
        IS_ON_BOARD(capX, capY) &
        
        // O movimento de captura deve ser um movimento válido
        fromX, fromY, toX, toY : CAPTURE_MOVES(board, turn) &
        
        // Se a captura é múltipla, a origem atual é obrigatoriamente o destino da anterior
        (comboPiece /= {} => mkPair(fromX, fromY) : comboPiece) &
        
        // Garante que 'capX' e 'capY' apontam de fato para a peça correta
        (
            (board(mkPair(fromX, fromY)) = (turn |-> man) & capX * 2 = fromX + toX & capY * 2 = fromY + toY) // Posição de captura é o ponto médio entre a origem e o destino
            or
            (board(mkPair(fromX, fromY)) = (turn |-> king) & mkPair(capX, capY) : DIAGONAL_PATH(fromX, fromY, toX, toY) /\ dom(board |> ({opponent(turn)} * TYPE)))  // Captura está entre a origem e destino e a casa está vazia
        )
    THEN
        LET next_board BE next_board = ({mkPair(fromX, fromY), mkPair(capX, capY)} <<| board) \/ {mkPair(toX, toY) |-> board(mkPair(fromX, fromY))} IN
            // Checa no "futuro" tabuleiro se a mesma peça tem mais capturas
            IF HAS_CONTINUOUS_CAPTURE(next_board, turn, toX, toY) THEN
                
                // Nenhuma das opções do THEN acima devem finalizar o jogo, pois há peças pra participar do combo
                SELECT board(mkPair(fromX, fromY)) = (turn |-> man) & ((turn = white & toX = MAX_COORD) or (turn = black & toX = MIN_COORD)) THEN // Só é possível escolher parar o combo quando há uma promoção no meio
                    turn := opponent(turn)
                    || comboPiece := {}
                    || board := ({mkPair(toX, toY)} <<| next_board) \/ {mkPair(toX, toY) |-> (turn |-> king)}
                WHEN 1 = 1 THEN  // Sempre é possível continuar o combo
                    // Desiste de virar dama e continua o combo
                    comboPiece := {mkPair(toX, toY)} // Tranca o turno na peça, negando virar dama para continuar o combo
                    || board := next_board
                END
                
            ELSE
                // As capturas que acontecem nessas condições podem finalizar o jogo
                board := next_board
                || turn := opponent(turn)  // Passa a vez e limpa a trava
                || comboPiece := {}
                || IF card(next_board |> ({opponent(turn)} * TYPE)) = 0 THEN
                       gameStatus := turnToWon(turn) // Perdeu por falta de peças
                   ELSIF not(HAS_AVAILABLE_MOVES_ON(next_board, opponent(turn))) THEN
                       gameStatus := turnToWon(turn) // Perdeu por falta de movimentos
                   END
            END
        END
    END;

    // Retorna TODAS as posições válidas de movimento para uma dada peça
    valid_moves <-- getPossibleMoves(fromX, fromY) =
    PRE
        fromX: INTEGER & fromY: INTEGER & 
        IS_ON_BOARD(fromX, fromY) &
        mkPair(fromX, fromY) : dom(board) &
        board(mkPair(fromX, fromY)) : {turn} * TYPE
    THEN
        valid_moves := { destX, destY | 
            destX: INTEGER & destY: INTEGER &
            fromX, fromY, destX, destY : NORMAL_MOVES(board, turn) \/ CAPTURE_MOVES(board, turn)
        }
    END;
    
    current_status <-- checkStatus=
    BEGIN
        current_status := gameStatus
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
