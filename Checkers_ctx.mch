/* Checkers_ctx
 * Author: Breno Jalmir
 * Creation date: 18/06/2026
 */
MACHINE Checkers_ctx

SETS
    PLAYER = {white, black, p_ee}; // white is 0, black is 1
    TYPE = {man, king, t_ee};
    STATUS = {playing, whiteWon, blackWon, draw};
    MOVE = {idle, moved, captured, huffed}

CONSTANTS
    MIN_COORD,
    MAX_COORD,
    MAX_MOVES
    
PROPERTIES
    MIN_COORD = 1 &
    MAX_COORD = 8 &
    MAX_MOVES = 32

END
