/* SpaceshipGame
 * Author: Sachintha Amarasiri
 * Creation date: 11/22/2021
 */
MACHINE
    SpaceshipGame

SETS 
    REPORT = {SUCCESSFULLY_MOVED, MOVEMENT_FAILED, MOVEMENT_FAILED_INSUFFICIENT_POWER, INVALID_MOVEMENT_OUT_OF_BOUND, MOVEMENT_FAILED_ASTEROID_COLLISION, WARP_DRIVE_MOVEMENT_SUCCESSFUL, INSUFFICIENT_POWER_WARP_DRIVE_MOVEMENT_FAILED, OUT_OF_BOUND_WARP_DRIVE_MOVEMENT_FAILED, ASTEROID_COLLISION_WARP_DRIVE_MOVEMENT_FAILED, WARP_DRIVE_MOVEMENT_FAILED, SPACESHIP_IS_DOCKED_AT_STARBASE, SPACESHIP_IS_NOT_AT_STARBASE, GAME_WON, GAME_LOST, GAME_NOT_OVER}
    
    
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
    gameStartPowerLevel
    
PROPERTIES
    // spaceGrid region 12 wide
    spaceGridX <: NAT1 & spaceGridX = 1..12 &
    
    // spaceGrid region 7 high
    spaceGridY <: NAT1 & spaceGridY = 1..7 &
    
    // spaceGrid made up regions
    spaceGrid =  spaceGridX * spaceGridY &
    
    // homeBase location
    homeBase = ( 1 |-> 1 ) &
    
    // starBase location
    starBase = ( 6 |-> 4 ) &
    
    // asteroids locations
    asteroid = { ( 7 |-> 1 ), ( 3 |-> 2 ), ( 11 |-> 2 ), ( 8 |-> 3 ), ( 5 |-> 4 ), ( 3 |-> 5 ), ( 7 |-> 5 ), ( 12 |-> 5 ), ( 10 |-> 6 ), ( 6 |-> 7 ), ( 7 |-> 7 ) } &
    
    normalMovePower = 5 &
    warpDrivePower = 20 &
    asteroidCollisionPowerLoss = 10 &
    
    // different power levels to start new game
    gameStartPowerLevel = { 150, 100, 50, 10 }
    
DEFINITIONS
    isSpaceshipInsideSpaceGrid( x_position, y_position ) == ( ( x_position |-> y_position ) : spaceGrid ) ;
    isAsteroidCollision( x_position, y_position ) == ( ( x_position |-> y_position ) : asteroid );
    isDocked == (spaceship_x |-> spaceship_y = starBase);
    isGameFinished == isDocked or (spaceship_power < normalMovePower)

VARIABLES
    spaceship_x, 
    spaceship_y,
    spaceship_power,
    no_of_collisions,
    spaceship_current_position,
    visited_route
    
INVARIANT
    spaceship_x : spaceGridX &
    spaceship_y : spaceGridY &
    spaceship_power : INTEGER &
    no_of_collisions : NAT &
    spaceship_current_position : spaceGrid &
    visited_route : seq( spaceGrid ) 
    
INITIALISATION
    spaceship_x := 1 || 
    spaceship_y := 1 ||
    spaceship_power := 0 ||
    no_of_collisions := 0 ||
    spaceship_current_position := ( homeBase ) || 
    visited_route := [ ( homeBase ) ] 
    
OPERATIONS
    
    // To start or re-start the game
    NewGame (power) =
    PRE
        isGameFinished & power:gameStartPowerLevel
    THEN
        spaceship_power := power ||
        no_of_collisions := 0 ||
        spaceship_x := 1 ||
        spaceship_y := 1 ||
        spaceship_current_position := ( homeBase ) || 
        visited_route := [( homeBase )] 
        
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
               // Check spaceship is at the starbase
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
                // Checks if the spaceship is inside the space grid if not displays an error message      
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
                    // Check spaceship is at the starbase
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
                // Checks if the spaceship is inside the space grid if not displays an error message      
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
                 // Check spaceship is at the starbase
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
             // Checks if the spaceship is inside the space grid if not displays an error message     
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
    
    // MoveBackward movement operation
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
                    // Check spaceship is at the starbase
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
                // Checks if the spaceship is inside the space grid if not displays an error message   
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
    
    // 
    report <-- EngageWarpDrive (newXPosition, newYPosition) = 
    PRE
        report : REPORT & newXPosition : NAT1 & newYPosition : NAT1 & not(isGameFinished)
        THEN
            // check power is enough to wrapDrive
            IF
                ( spaceship_power >= warpDrivePower )
            THEN
                // Checks spaceship is inside the space grid and not hit an asteroid 
                IF
                    ( isSpaceshipInsideSpaceGrid( newXPosition, newYPosition ) & not( isAsteroidCollision( newXPosition, newYPosition ) ) ) 
                THEN
                    // Check spaceship is at the starbase
                    IF
                        ( ( newXPosition |-> newYPosition ) = starBase ) 
                    THEN
                        spaceship_x, spaceship_y := newXPosition, newYPosition
                        || spaceship_current_position := ( newXPosition |-> newYPosition )
                        || spaceship_power := spaceship_power - warpDrivePower
                        || visited_route := visited_route ^ [ newXPosition |-> newYPosition ]
                        || report := GAME_WON
                    ELSE
                        // check spaceship power is enough to next movement after warp drive
                        IF
                            ( ( spaceship_power - warpDrivePower ) >= normalMovePower ) 
                        THEN
                            spaceship_x, spaceship_y := newXPosition, newYPosition
                            || spaceship_current_position := ( newXPosition |-> newYPosition )
                            || spaceship_power := spaceship_power - warpDrivePower
                            || visited_route := visited_route ^ [ newXPosition |-> newYPosition ]
                            || report := WARP_DRIVE_MOVEMENT_SUCCESSFUL
                        ELSE
                            spaceship_x, spaceship_y := newXPosition, newYPosition
                            || spaceship_current_position := ( newXPosition |-> newYPosition )
                            || spaceship_power := spaceship_power - warpDrivePower
                            || visited_route := visited_route ^ [ newXPosition |-> newYPosition ]
                            || report := GAME_LOST
                        END
                    END
                ELSIF
                    ( isAsteroidCollision( newXPosition, newYPosition ) )
                THEN
                    // check power is enough to continue game after hit an asteroid
                    IF
                        ( ( spaceship_power - asteroidCollisionPowerLoss ) >= normalMovePower )
                    THEN
                        no_of_collisions := no_of_collisions + 1
                        || report := ASTEROID_COLLISION_WARP_DRIVE_MOVEMENT_FAILED
                    ELSE
                        no_of_collisions := no_of_collisions + 1
                        || report := GAME_LOST
                    END
                // Checks if the spaceship is inside the space grid if not displays an error message 
                ELSIF
                    ( not( isSpaceshipInsideSpaceGrid( newXPosition, newYPosition ) ) )
                THEN
                    report := OUT_OF_BOUND_WARP_DRIVE_MOVEMENT_FAILED
                ELSE
                    report := WARP_DRIVE_MOVEMENT_FAILED
                END
        // If the power is not enough, displays an insufficient power message   
        ELSE
            report := INSUFFICIENT_POWER_WARP_DRIVE_MOVEMENT_FAILED
        END
       END;
    
    // Reports the current status of the spaceship
    currentLocation, currentPowerReserve, noOfAsteroidCollisions <-- MissionStatus =
    BEGIN
        currentLocation := spaceship_current_position ||
        currentPowerReserve := spaceship_power ||
        noOfAsteroidCollisions := no_of_collisions
    END;
    
    // Reports the regions of space that the spaceship has traveled through
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
