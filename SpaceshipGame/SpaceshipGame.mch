/* SpaceshipGame
 * Author: Sachintha Amarasiri
 * Creation date: 11/22/2021
 */
MACHINE
    SpaceshipGame

SETS 
    REPORT = {MOVEMENT_SUCCESSFUL, MOVEMENT_SUCCESSFUL_AND_GAME_WON, MOVEMENT_FAILED, MOVEMENT_FAILED_INSUFFICIENT_POWER, INVALID_MOVEMENT_OUT_OF_BOUND, MOVEMENT_FAILED_ASTEROID_COLLISION, MOVEMENT_SUCCESSFUL_BUT_GAME_LOST_INSUFFICIENT_POWER_FOR_NEXT_MOVEMENT, ASTEROID_COLLISION_AND_GAME_LOST_INSUFFICIENT_POWER_FOR_NEXT_MOVEMENT, WARP_DRIVE_MOVEMENT_SUCCESSFUL, INSUFFICIENT_POWER_WARP_DRIVE_MOVEMENT_FAILED, OUT_OF_BOUND_WARP_DRIVE_MOVEMENT_FAILED, CANNOT_WARP_DRIVE_DUE_TO_ASTEROID, WARP_DRIVE_MOVEMENT_FAILED, SPACESHIP_IS_DOCKED_AT_STARBASE, SPACESHIP_IS_NOT_AT_STARBASE, GAME_WON, GAME_LOST, GAME_NOT_OVER};
    SPACESHIP_MOVEMENT = {MOVE_UP, MOVE_DOWN, MOVE_FORWARD, MOVE_BACKWARD, WARP_DRIVE}
        
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
    
    // spaceGrid is made up squares of the grid(regions)
    spaceGrid =  spaceGridX * spaceGridY &
    
    // homeBase location
    homeBase : spaceGrid &
    homeBase = ( 1 |-> 1 ) &
    
    // starBase location
    starBase : spaceGrid &
    starBase = ( 6 |-> 4 ) &
    
    // asteroids locations
    asteroid <: spaceGrid &
    asteroid = { ( 7 |-> 1 ), ( 3 |-> 2 ), ( 11 |-> 2 ), ( 8 |-> 3 ), ( 5 |-> 4 ), ( 3 |-> 5 ), ( 7 |-> 5 ), ( 12 |-> 5 ), ( 10 |-> 6 ), ( 6 |-> 7 ), ( 7 |-> 7 ) } &
    
    // spaceship uses up powers for movements and loses power if spaceship crashes into a asteroid 
    normalMovePower = 5 &
    warpDrivePower = 20 &
    asteroidCollisionPowerLoss = 10 &
    
    // different power levels to start new game
    gameStartPowerLevel = { 10, 50, 100, 150 }
    
DEFINITIONS
    isSpaceshipInsideSpaceGrid( x_position, y_position ) == ( ( x_position |-> y_position ) : spaceGrid ) ;
    isAsteroidCollision( x_position, y_position ) == ( ( x_position |-> y_position ) : asteroid );
    isDockedAtStarBase == (spaceship_x |-> spaceship_y = starBase);
    isGameOver == isDockedAtStarBase or (spaceship_power < normalMovePower)

VARIABLES
    spaceship_x, 
    spaceship_y,
    spaceship_power,
    no_of_collisions,
    spaceship_current_position,
    visited_region,
    spaceship_movements
    
INVARIANT
    spaceship_x : spaceGridX &
    spaceship_y : spaceGridY &
    spaceship_power : INTEGER &
    no_of_collisions : NAT &
    spaceship_current_position : spaceGrid &
    visited_region : seq( spaceGrid ) &
    spaceship_movements : seq( SPACESHIP_MOVEMENT )
    
INITIALISATION
    spaceship_x := 1 || 
    spaceship_y := 1 ||
    spaceship_power := 0 ||
    no_of_collisions := 0 ||
    spaceship_current_position := ( homeBase ) || 
    visited_region := [ ( homeBase ) ] ||
    spaceship_movements := []
    
OPERATIONS
    
    // To start or re-start the game
    NewGame (power) =
    PRE
        power:gameStartPowerLevel
    THEN
        spaceship_current_position := ( homeBase )
        || spaceship_power := power 
        || no_of_collisions := 0 
        || visited_region := [( homeBase )] 
        || spaceship_x := 1 
        || spaceship_y := 1  
        || spaceship_movements := []
    END;
    
    // MoveUp movement operation
    report <-- MoveUp = 
    PRE
        report : REPORT & not(isGameOver)   
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
                   || visited_region := visited_region ^ [ spaceship_x |-> succ( spaceship_y ) ]
                   || spaceship_movements := spaceship_movements <- MOVE_UP
                   || report := MOVEMENT_SUCCESSFUL_AND_GAME_WON
               ELSE
               // Check spaceship power is enough to next movement
               IF
                   ( (spaceship_power - normalMovePower) >= normalMovePower )
               THEN
                   spaceship_x, spaceship_y := spaceship_x, succ( spaceship_y )
                   || spaceship_current_position := ( spaceship_x |-> succ( spaceship_y ) )
                   || spaceship_power := spaceship_power - normalMovePower
                   || visited_region := visited_region ^ [ spaceship_x |-> succ( spaceship_y ) ]
                   || spaceship_movements := spaceship_movements <- MOVE_UP
                   || report := MOVEMENT_SUCCESSFUL
               ELSE
                   spaceship_x, spaceship_y := spaceship_x, succ( spaceship_y )
                   || spaceship_current_position := ( spaceship_x |-> succ( spaceship_y ) )
                   || spaceship_power := spaceship_power - normalMovePower
                   || visited_region := visited_region ^ [ spaceship_x |-> succ( spaceship_y ) ]
                   || spaceship_movements := spaceship_movements <- MOVE_UP
                   || report := MOVEMENT_SUCCESSFUL_BUT_GAME_LOST_INSUFFICIENT_POWER_FOR_NEXT_MOVEMENT
               END
           END
           // Check spaceship hit an asteroid
           ELSIF
               ( isAsteroidCollision( spaceship_x, succ( spaceship_y ) ) )
           THEN
               // Checks the power will be enough to continue the game after the hit an asteroid
               IF
                   ( ( spaceship_power - asteroidCollisionPowerLoss ) >= normalMovePower )
               THEN
                   no_of_collisions := succ(no_of_collisions)
                   || spaceship_power  := spaceship_power - asteroidCollisionPowerLoss
                   || report := MOVEMENT_FAILED_ASTEROID_COLLISION
               ELSE
                   no_of_collisions := succ(no_of_collisions)
                   || spaceship_power  := spaceship_power - asteroidCollisionPowerLoss
                   || report := ASTEROID_COLLISION_AND_GAME_LOST_INSUFFICIENT_POWER_FOR_NEXT_MOVEMENT
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
        report : REPORT & not(isGameOver)   
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
                     || visited_region := visited_region ^ [ spaceship_x |-> pred( spaceship_y ) ]
                     || spaceship_movements := spaceship_movements <- MOVE_DOWN
                     || report := MOVEMENT_SUCCESSFUL_AND_GAME_WON
                 ELSE
                     // Check spaceship power is enough to next movement
                     IF
                         ( (spaceship_power - normalMovePower) >= normalMovePower )
                     THEN
                         spaceship_x, spaceship_y := spaceship_x, pred( spaceship_y )
                         || spaceship_current_position := ( spaceship_x |-> pred( spaceship_y ) )
                         || spaceship_power := spaceship_power - normalMovePower
                         || visited_region := visited_region ^ [ spaceship_x |-> pred( spaceship_y ) ]
                         || spaceship_movements := spaceship_movements <- MOVE_DOWN
                         || report := MOVEMENT_SUCCESSFUL
                     ELSE
                         spaceship_x, spaceship_y := spaceship_x, pred( spaceship_y )
                         || spaceship_current_position := ( spaceship_x |-> pred( spaceship_y ) )
                         || spaceship_power := spaceship_power - normalMovePower
                         || visited_region := visited_region ^ [ spaceship_x |-> pred( spaceship_y ) ]
                         || spaceship_movements := spaceship_movements <- MOVE_DOWN
                         || report := MOVEMENT_SUCCESSFUL_BUT_GAME_LOST_INSUFFICIENT_POWER_FOR_NEXT_MOVEMENT
                     END
                 END
             // Check spaceship hit an asteroid
             ELSIF
                 ( isAsteroidCollision( spaceship_x, pred( spaceship_y ) ) )
             THEN
                 // Checks the power will be enough to continue the game after the hit an asteroid
                 IF
                     ( ( spaceship_power - asteroidCollisionPowerLoss ) >= normalMovePower )
                 THEN
                     no_of_collisions := succ(no_of_collisions)
                     || spaceship_power  := spaceship_power - asteroidCollisionPowerLoss
                     || report := MOVEMENT_FAILED_ASTEROID_COLLISION
                 ELSE
                     no_of_collisions := succ(no_of_collisions)
                     || spaceship_power  := spaceship_power - asteroidCollisionPowerLoss
                     || report := ASTEROID_COLLISION_AND_GAME_LOST_INSUFFICIENT_POWER_FOR_NEXT_MOVEMENT
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
        report : REPORT & not(isGameOver)   
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
                    || visited_region := visited_region ^ [ succ(spaceship_x) |-> spaceship_y ]
                    || spaceship_movements := spaceship_movements <- MOVE_FORWARD
                    || report := MOVEMENT_SUCCESSFUL_AND_GAME_WON
                ELSE
                    // Check spaceship power is enough to next movement
                    IF
                        ( (spaceship_power - normalMovePower) >= normalMovePower )
                    THEN
                        spaceship_x, spaceship_y := succ(spaceship_x), spaceship_y
                        || spaceship_current_position := ( succ(spaceship_x) |-> spaceship_y )
                        || spaceship_power := spaceship_power - normalMovePower
                        || visited_region := visited_region ^ [ succ(spaceship_x) |-> spaceship_y ]
                        || spaceship_movements := spaceship_movements <- MOVE_FORWARD
                        || report := MOVEMENT_SUCCESSFUL
                    ELSE
                        spaceship_x, spaceship_y := succ(spaceship_x), spaceship_y
                        || spaceship_current_position := ( succ(spaceship_x) |-> spaceship_y )
                        || spaceship_power := spaceship_power - normalMovePower
                        || visited_region := visited_region ^ [ succ(spaceship_x) |-> spaceship_y ]
                        || spaceship_movements := spaceship_movements <- MOVE_FORWARD
                        || report := MOVEMENT_SUCCESSFUL_BUT_GAME_LOST_INSUFFICIENT_POWER_FOR_NEXT_MOVEMENT
                    END
                END
            // Check spaceship hit an asteroid
            ELSIF
                ( isAsteroidCollision( succ(spaceship_x), spaceship_y ) )
            THEN
                // Checks the power will be enough to continue the game after the hit an asteroid
                IF
                    ( ( spaceship_power - asteroidCollisionPowerLoss ) >= normalMovePower )
                THEN
                    no_of_collisions := succ(no_of_collisions)
                    || spaceship_power  := spaceship_power - asteroidCollisionPowerLoss
                    || report := MOVEMENT_FAILED_ASTEROID_COLLISION
                ELSE
                    no_of_collisions := succ(no_of_collisions)
                    || spaceship_power  := spaceship_power - asteroidCollisionPowerLoss
                    || report := ASTEROID_COLLISION_AND_GAME_LOST_INSUFFICIENT_POWER_FOR_NEXT_MOVEMENT
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
        report : REPORT & not(isGameOver)   
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
                    || visited_region := visited_region ^ [ pred(spaceship_x) |-> spaceship_y ]
                    || spaceship_movements := spaceship_movements <- MOVE_BACKWARD
                    || report := MOVEMENT_SUCCESSFUL_AND_GAME_WON
                ELSE
                    // Check spaceship power is enough to next movement
                    IF
                        ( (spaceship_power - normalMovePower) >= normalMovePower )
                    THEN
                        spaceship_x, spaceship_y := pred(spaceship_x), spaceship_y
                        || spaceship_current_position := ( pred(spaceship_x) |-> spaceship_y )
                        || spaceship_power := spaceship_power - normalMovePower
                        || visited_region := visited_region ^ [ pred(spaceship_x) |-> spaceship_y ]
                        || spaceship_movements := spaceship_movements <- MOVE_BACKWARD
                        || report := MOVEMENT_SUCCESSFUL
                    ELSE
                        spaceship_x, spaceship_y := pred(spaceship_x), spaceship_y
                        || spaceship_current_position := ( pred(spaceship_x) |-> spaceship_y )
                        || spaceship_power := spaceship_power - normalMovePower
                        || visited_region := visited_region ^ [ pred(spaceship_x) |-> spaceship_y ]
                        || spaceship_movements := spaceship_movements <- MOVE_BACKWARD
                        || report := MOVEMENT_SUCCESSFUL_BUT_GAME_LOST_INSUFFICIENT_POWER_FOR_NEXT_MOVEMENT
                    END
                END
            // Check spaceship hit an asteroid
            ELSIF
                ( isAsteroidCollision( pred(spaceship_x), spaceship_y ) )
            THEN
                // Checks the power will be enough to continue the game after the hit an asteroid
                IF
                    ( ( spaceship_power - asteroidCollisionPowerLoss ) >= normalMovePower )
                THEN
                    no_of_collisions := succ(no_of_collisions)
                    || spaceship_power  := spaceship_power - asteroidCollisionPowerLoss
                    || report := MOVEMENT_FAILED_ASTEROID_COLLISION
                ELSE
                    no_of_collisions := succ(no_of_collisions)
                    || spaceship_power  := spaceship_power - asteroidCollisionPowerLoss
                    || report := ASTEROID_COLLISION_AND_GAME_LOST_INSUFFICIENT_POWER_FOR_NEXT_MOVEMENT
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
    
    // Warp-drive Spaceship Movement
    report <-- EngageWarpDrive (newXPosition, newYPosition) = 
    PRE
        report : REPORT & newXPosition : NAT1 & newYPosition : NAT1 & not(isGameOver)
    THEN
        // Check power is enough to WrapDrive
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
                    || visited_region := visited_region ^ [ newXPosition |-> newYPosition ]
                    || spaceship_movements := spaceship_movements <- WARP_DRIVE
                    || report := MOVEMENT_SUCCESSFUL_AND_GAME_WON
                ELSE
                    // Check spaceship power is enough to next movement after warp drive
                    IF
                        ( ( spaceship_power - warpDrivePower ) >= normalMovePower ) 
                    THEN
                        spaceship_x, spaceship_y := newXPosition, newYPosition
                        || spaceship_current_position := ( newXPosition |-> newYPosition )
                        || spaceship_power := spaceship_power - warpDrivePower
                        || visited_region := visited_region ^ [ newXPosition |-> newYPosition ]
                        || spaceship_movements := spaceship_movements <- WARP_DRIVE
                        || report := WARP_DRIVE_MOVEMENT_SUCCESSFUL
                    ELSE
                        spaceship_x, spaceship_y := newXPosition, newYPosition
                        || spaceship_current_position := ( newXPosition |-> newYPosition )
                        || spaceship_power := spaceship_power - warpDrivePower
                        || visited_region := visited_region ^ [ newXPosition |-> newYPosition ]
                        || spaceship_movements := spaceship_movements <- WARP_DRIVE
                        || report := MOVEMENT_SUCCESSFUL_BUT_GAME_LOST_INSUFFICIENT_POWER_FOR_NEXT_MOVEMENT
                    END
                END
            // If asteroid collisions display warp-drive cannot be used because of position is occupied by an asteroid     
            ELSIF
                ( isAsteroidCollision( newXPosition, newYPosition ) )
            THEN
                 report := CANNOT_WARP_DRIVE_DUE_TO_ASTEROID
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
        currentLocation := spaceship_current_position
        || currentPowerReserve := spaceship_power 
        || noOfAsteroidCollisions := no_of_collisions
    END;
    
    // Reports the regions of space that the spaceship has traveled through
    region <-- RegionsVisited =
    BEGIN
        region := visited_region
    END;
    
    // Reports whether the Spaceship is “docked” at the starbase
    report <-- DockedAtStarbase =
    PRE
        report : REPORT  
    THEN
        IF
            (isDockedAtStarBase)
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
            (isDockedAtStarBase)
        THEN
            report := GAME_WON
        ELSE
            IF
                not(isDockedAtStarBase) & (spaceship_power < normalMovePower)
            THEN
                report := GAME_LOST
            ELSE
                report := GAME_NOT_OVER
            END
        END
    END   
END