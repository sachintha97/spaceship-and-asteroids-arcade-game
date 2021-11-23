/* SpaceshipGame
 * Author: Sachintha Amarasiri
 * Creation date: 11/22/2021
 */
MACHINE
    SpaceshipGame

SETS 
    //GAME_STATUS = { GameWON, GameLOST, GameNotOver };
    REPORT = {SUCCESSFULLY_MOVED, MOVEMENT_FAILED, MOVEMENT_FAILED_INSUFFICIENT_POWER, INVALID_MOVEMENT_OUT_OF_BOUND, MOVEMENT_FAILED_ASTEROID_COLLISION,
        CANNOT_WARP_INTO_ASTEROID, CANNOT_WARP_TO_THE_SAME_POSITION, CANNOT_IMMEDIATELY_WARP_INTO_STARBASE, 
        SPACESHIP_IS_DOCKED_AT_STARBASE, SPACESHIP_IS_NOT_AT_STARBASE, 
        GAME_WON, GAME_LOST, GAME_NOT_OVER}
    
    
CONSTANTS
    spaceGridX,
    spaceGridY,
    spaceGrid,
    homeBase,
    starBase,
    asteroid,
    normalMovePower, 
    warpDrivePower, 
    asteroidCollisionPowerLoss,
    powerLevel
    
PROPERTIES
    spaceGridX <: NAT1 & spaceGridX = 1..12 &
    spaceGridY <: NAT1 & spaceGridY = 1..7 &
    
    //spaceGrid : GRID &
    spaceGrid =  spaceGridX * spaceGridY &
    
    //homeBase : GRID &
    homeBase = ( 1 |-> 1 ) &
    
    //starBase : GRID &
    starBase = ( 6 |-> 4 ) &
    
    // asteroids locations
    //asteroid : GRID &
    asteroid = { ( 7 |-> 1 ), ( 3 |-> 2 ), ( 11 |-> 2 ), ( 8 |-> 3 ), ( 5 |-> 4 ), ( 3 |-> 5 ), ( 7 |-> 5 ), ( 12 |-> 5 ), ( 10 |-> 6 ), ( 6 |-> 7 ), ( 7 |-> 7 ) } &
    
    normalMovePower = 5 &
    warpDrivePower = 20 &
    asteroidCollisionPowerLoss = 10 &
    powerLevel = {120}
    
DEFINITIONS
    //GRID == POW( NAT1 * NAT1 );
    isSpaceshipInsideSpaceGrid( xx, yy ) == ( ( xx |-> yy ) : spaceGrid ) ;
    isAsteroidCollision( xx, yy ) == ( ( xx |-> yy ) : asteroid );
    isDocked == (spaceship_x |-> spaceship_y = starBase);
    isGameFinished == isDocked or (spaceship_power < normalMovePower)

VARIABLES
    spaceship_x, //    spaceshipX,
    spaceship_y, //    spaceshipY,
    spaceship_power, //    spaceshipPower,
    no_of_collisions, //    noOfAsteroidCollisions,
    spaceship_current_position, //    spaceshipCurrentPosition,
    visited_route //    spaceshipRoute,
    
INVARIANT
    spaceship_x : spaceGridX &
    spaceship_y : spaceGridY &
    //spaceship_x |-> spaceship_y : spaceGrid &
    spaceship_power : INTEGER &
    no_of_collisions : NAT &
    spaceship_current_position : spaceGrid &
    visited_route : seq( spaceGrid ) 
    
INITIALISATION
    spaceship_x := 1 || 
    spaceship_y := 1 ||
    spaceship_power := 0 ||
    no_of_collisions := 0 ||
    spaceship_current_position := ( 1 |-> 1 ) || 
    visited_route := [ ( 1 |-> 1 ) ] 
    
OPERATIONS
    
    // To start or re-start the game
    NewGame (power) =
    PRE
        isGameFinished & power:powerLevel
    THEN
        //power := spaceship_power(power) ||
        spaceship_power := power ||
        no_of_collisions := 0 ||
        spaceship_x := 1 ||
        spaceship_y := 1 ||
        visited_route := [( 1 |-> 1 )] 
        
    END;
    
    // MoveUp movement operation
    report <-- MoveUp = 
    PRE
        report : REPORT & not(isGameFinished)   
    THEN
        IF
            ( spaceship_power >= normalMovePower )
            THEN
                //Checks spaceship is inside the space grid and not hit an asteroid 
                IF
                    ( isSpaceshipInsideSpaceGrid( spaceship_x, succ( spaceship_y ) ) & not( isAsteroidCollision( spaceship_x, succ( spaceship_y ) ) ) )
                THEN
                    // Check spaceship is “docked” at the starbase
                    IF
                        (spaceship_x  |-> succ(spaceship_y) = starBase)
                    THEN
                        spaceship_x, spaceship_y := spaceship_x, succ( spaceship_y )
                        || spaceship_current_position := ( spaceship_x |-> succ( spaceship_y ) ) 
                        || spaceship_power := spaceship_power - normalMovePower
                        || visited_route := visited_route ^ [ spaceship_x |-> succ( spaceship_y ) ]
                        || report := GAME_WON
                    ELSE
                        // check spaceship power is enough to next moveUp movement
                        IF
                            ( (spaceship_power - normalMovePower) >= normalMovePower )
                        THEN
                            spaceship_x, spaceship_y := spaceship_x, succ( spaceship_y )
                            || spaceship_current_position := ( spaceship_x |-> succ( spaceship_y ) )
                            || spaceship_power := spaceship_power - normalMovePower
                            || visited_route := visited_route ^ [ spaceship_x |-> succ( spaceship_y ) ]
                            || report := SUCCESSFULLY_MOVED
                        ELSE
                            spaceship_x, spaceship_y := spaceship_x, succ( spaceship_y )
                            || spaceship_current_position := ( spaceship_x |-> succ( spaceship_y ) )
                            || spaceship_power := spaceship_power - normalMovePower
                            || visited_route := visited_route ^ [ spaceship_x |-> succ( spaceship_y ) ]
                            || report := GAME_LOST
                        END
                    END
                   // check spaceship hit an asteroid
                ELSIF
                    ( isAsteroidCollision( spaceship_x, succ( spaceship_y ) ) )
                THEN
                    // Checks the power will be enough to continue the game after the hit an asteroid
                    IF
                        ( ( spaceship_power - asteroidCollisionPowerLoss ) >= normalMovePower )
                    THEN
                        no_of_collisions := no_of_collisions + 1
                        || spaceship_power  := spaceship_power - asteroidCollisionPowerLoss
                        || report := MOVEMENT_FAILED_ASTEROID_COLLISION
                    ELSE
                        no_of_collisions := no_of_collisions + 1
                        || spaceship_power  := spaceship_power - asteroidCollisionPowerLoss
                        || report := GAME_LOST
                    END
                    // Checks if the spaceship is not inside the space grid     
                ELSIF
                    ( not( isSpaceshipInsideSpaceGrid( spaceship_x, succ( spaceship_y ) ) ) )
                THEN
                    report := INVALID_MOVEMENT_OUT_OF_BOUND
                ELSE
                    report := MOVEMENT_FAILED
                END
                // If the power is not enough displays an insufficient power message   
            ELSE
                report := MOVEMENT_FAILED_INSUFFICIENT_POWER
            END       
    END;
    
    // MoveDown movement operation
    report <-- MoveDown = 
    PRE
        report : REPORT & not(isGameFinished)   
    THEN
        IF
            ( spaceship_power >= normalMovePower )
            THEN
                //Checks spaceship is inside the space grid and not hit an asteroid 
                IF
                    ( isSpaceshipInsideSpaceGrid( spaceship_x, pred( spaceship_y ) ) & not( isAsteroidCollision( spaceship_x, pred( spaceship_y ) ) ) )
                THEN
                    // Check spaceship is “docked” at the starbase
                    IF
                        (spaceship_x  |-> pred(spaceship_y) = starBase)
                    THEN
                        spaceship_x, spaceship_y := spaceship_x, pred( spaceship_y )
                        || spaceship_current_position := ( spaceship_x |-> pred( spaceship_y ) ) 
                        || spaceship_power := spaceship_power - normalMovePower
                        || visited_route := visited_route ^ [ spaceship_x |-> pred( spaceship_y ) ]
                        || report := GAME_WON
                    ELSE
                        // check spaceship power is enough to next MoveDown movement
                        IF
                            ( (spaceship_power - normalMovePower) >= normalMovePower )
                        THEN
                            spaceship_x, spaceship_y := spaceship_x, pred( spaceship_y )
                            || spaceship_current_position := ( spaceship_x |-> pred( spaceship_y ) )
                            || spaceship_power := spaceship_power - normalMovePower
                            || visited_route := visited_route ^ [ spaceship_x |-> pred( spaceship_y ) ]
                            || report := SUCCESSFULLY_MOVED
                        ELSE
                            spaceship_x, spaceship_y := spaceship_x, pred( spaceship_y )
                            || spaceship_current_position := ( spaceship_x |-> pred( spaceship_y ) )
                            || spaceship_power := spaceship_power - normalMovePower
                            || visited_route := visited_route ^ [ spaceship_x |-> pred( spaceship_y ) ]
                            || report := GAME_LOST
                        END
                    END
                   // check spaceship hit an asteroid
                ELSIF
                    ( isAsteroidCollision( spaceship_x, pred( spaceship_y ) ) )
                THEN
                    // Checks the power will be enough to continue the game after the hit an asteroid
                    IF
                        ( ( spaceship_power - asteroidCollisionPowerLoss ) >= normalMovePower )
                    THEN
                        no_of_collisions := no_of_collisions + 1
                        || spaceship_power  := spaceship_power - asteroidCollisionPowerLoss
                        || report := MOVEMENT_FAILED_ASTEROID_COLLISION
                    ELSE
                        no_of_collisions := no_of_collisions + 1
                        || spaceship_power  := spaceship_power - asteroidCollisionPowerLoss
                        || report := GAME_LOST
                    END
                    // Checks if the spaceship is not inside the space grid     
                ELSIF
                    ( not( isSpaceshipInsideSpaceGrid( spaceship_x, pred( spaceship_y ) ) ) )
                THEN
                    report := INVALID_MOVEMENT_OUT_OF_BOUND
                ELSE
                    report := MOVEMENT_FAILED
                END
                // If the power is not enough displays an insufficient power message   
            ELSE
                report := MOVEMENT_FAILED_INSUFFICIENT_POWER
            END       
    END;        
    
    // MoveForward movement operation
    report <-- MoveForward = 
    PRE
        report : REPORT & not(isGameFinished)   
    THEN
        IF
            ( spaceship_power >= normalMovePower )
            THEN
                //Checks spaceship is inside the space grid and not hit an asteroid 
                IF
                    ( isSpaceshipInsideSpaceGrid( succ(spaceship_x), spaceship_y ) & not( isAsteroidCollision( succ(spaceship_x), spaceship_y ) ) )
                THEN
                    // Check spaceship is “docked” at the starbase
                    IF
                        (succ(spaceship_x)  |-> spaceship_y = starBase)
                    THEN
                        spaceship_x, spaceship_y := succ(spaceship_x), spaceship_y 
                        || spaceship_current_position := ( succ(spaceship_x) |-> spaceship_y ) 
                        || spaceship_power := spaceship_power - normalMovePower
                        || visited_route := visited_route ^ [ succ(spaceship_x) |-> spaceship_y ]
                        || report := GAME_WON
                    ELSE
                        // check spaceship power is enough to next MoveForward movement
                        IF
                            ( (spaceship_power - normalMovePower) >= normalMovePower )
                        THEN
                            spaceship_x, spaceship_y := succ(spaceship_x), spaceship_y
                            || spaceship_current_position := ( succ(spaceship_x) |-> spaceship_y )
                            || spaceship_power := spaceship_power - normalMovePower
                            || visited_route := visited_route ^ [ succ(spaceship_x) |-> spaceship_y ]
                            || report := SUCCESSFULLY_MOVED
                        ELSE
                            spaceship_x, spaceship_y := succ(spaceship_x), spaceship_y
                            || spaceship_current_position := ( succ(spaceship_x) |-> spaceship_y )
                            || spaceship_power := spaceship_power - normalMovePower
                            || visited_route := visited_route ^ [ succ(spaceship_x) |-> spaceship_y ]
                            || report := GAME_LOST
                        END
                    END
                   // check spaceship hit an asteroid
                ELSIF
                    ( isAsteroidCollision( succ(spaceship_x), spaceship_y ) )
                THEN
                    // Checks the power will be enough to continue the game after the hit an asteroid
                    IF
                        ( ( spaceship_power - asteroidCollisionPowerLoss ) >= normalMovePower )
                    THEN
                        no_of_collisions := no_of_collisions + 1
                        || spaceship_power  := spaceship_power - asteroidCollisionPowerLoss
                        || report := MOVEMENT_FAILED_ASTEROID_COLLISION
                    ELSE
                        no_of_collisions := no_of_collisions + 1
                        || spaceship_power  := spaceship_power - asteroidCollisionPowerLoss
                        || report := GAME_LOST
                    END
                    // Checks if the spaceship is not inside the space grid     
                ELSIF
                    ( not( isSpaceshipInsideSpaceGrid( succ(spaceship_x), spaceship_y  ) ) )
                THEN
                    report := INVALID_MOVEMENT_OUT_OF_BOUND
                ELSE
                    report := MOVEMENT_FAILED
                END
                // If the power is not enough displays an insufficient power message   
            ELSE
                report := MOVEMENT_FAILED_INSUFFICIENT_POWER
            END       
    END;
    
     // MoveForward movement operation
    report <-- MoveBackward = 
    PRE
        report : REPORT & not(isGameFinished)   
    THEN
        IF
            ( spaceship_power >= normalMovePower )
            THEN
                //Checks spaceship is inside the space grid and not hit an asteroid 
                IF
                    ( isSpaceshipInsideSpaceGrid( pred(spaceship_x), spaceship_y ) & not( isAsteroidCollision( pred(spaceship_x), spaceship_y ) ) )
                THEN
                    // Check spaceship is “docked” at the starbase
                    IF
                       (pred(spaceship_x)  |-> spaceship_y = starBase)
                    THEN
                        spaceship_x, spaceship_y := pred(spaceship_x), spaceship_y 
                        || spaceship_current_position := ( pred(spaceship_x) |-> spaceship_y ) 
                        || spaceship_power := spaceship_power - normalMovePower
                        || visited_route := visited_route ^ [ pred(spaceship_x) |-> spaceship_y ]
                        || report := GAME_WON
                    ELSE
                        // check spaceship power is enough to next MoveBackward movement
                        IF
                            ( (spaceship_power - normalMovePower) >= normalMovePower )
                        THEN
                            spaceship_x, spaceship_y := pred(spaceship_x), spaceship_y
                            || spaceship_current_position := ( pred(spaceship_x) |-> spaceship_y )
                            || spaceship_power := spaceship_power - normalMovePower
                            || visited_route := visited_route ^ [ pred(spaceship_x) |-> spaceship_y ]
                            || report := SUCCESSFULLY_MOVED
                        ELSE
                            spaceship_x, spaceship_y := pred(spaceship_x), spaceship_y
                            || spaceship_current_position := ( pred(spaceship_x) |-> spaceship_y )
                            || spaceship_power := spaceship_power - normalMovePower
                            || visited_route := visited_route ^ [ pred(spaceship_x) |-> spaceship_y ]
                            || report := GAME_LOST
                        END
                    END
                   // check spaceship hit an asteroid
                ELSIF
                    ( isAsteroidCollision( pred(spaceship_x), spaceship_y ) )
                THEN
                    // Checks the power will be enough to continue the game after the hit an asteroid
                    IF
                        ( ( spaceship_power - asteroidCollisionPowerLoss ) >= normalMovePower )
                    THEN
                        no_of_collisions := no_of_collisions + 1
                        || spaceship_power  := spaceship_power - asteroidCollisionPowerLoss
                        || report := MOVEMENT_FAILED_ASTEROID_COLLISION
                    ELSE
                        no_of_collisions := no_of_collisions + 1
                        || spaceship_power  := spaceship_power - asteroidCollisionPowerLoss
                        || report := GAME_LOST
                    END
                    // Checks if the spaceship is not inside the space grid     
                ELSIF
                    ( not( isSpaceshipInsideSpaceGrid( pred(spaceship_x), spaceship_y  ) ) )
                THEN
                    report := INVALID_MOVEMENT_OUT_OF_BOUND
                ELSE
                    report := MOVEMENT_FAILED
                END
                // If the power is not enough displays an insufficient power message   
            ELSE
                report := MOVEMENT_FAILED_INSUFFICIENT_POWER
            END       
    END;
    
    // Reports the current status of the spaceship
    currentLocation, currentPowerReserve, noOfAsteroidCollisions <-- MissionStatus =
    BEGIN
        currentLocation := spaceship_current_position ||
        currentPowerReserve := spaceship_power ||
        noOfAsteroidCollisions := no_of_collisions
    END;
    
    // Reports the regions of space that the spaceship has travelled through
    report <-- RegionsVisited =
    BEGIN
        report := visited_route
    END;
    
    // Reports whether the Spaceship is “docked” at the starbase
    report <-- DockedAtStarbase =
    PRE
        report : REPORT  
    THEN
        IF
            (isDocked)
        THEN
            report := SPACESHIP_IS_DOCKED_AT_STARBASE
        ELSE
            report := SPACESHIP_IS_NOT_AT_STARBASE
        END
    END;

    // GameStatus that reports
    report <-- GameStatus =
    PRE
        report : REPORT
    THEN
        IF
            (isDocked)
        THEN
            report := GAME_WON
        ELSE
            IF
                not(isDocked) & (spaceship_power < normalMovePower)
            THEN
                report := GAME_LOST
            ELSE
                report := GAME_NOT_OVER
            END
        END
    END
END
