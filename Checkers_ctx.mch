MACHINE Checkers_ctx

SETS
    PLAYER = {white, black};
    TYPE = {man, king};
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
