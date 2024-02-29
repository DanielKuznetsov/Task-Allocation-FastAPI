from z3 import *

def create_solver(robots, tasks, rooms, weighted_edges, T, capacity=1):
    # Create variables
    b_rooms = [[[Bool('robotID'+str(robot.id)+"_timeStep"+str(t)+'_room'+str(room))
                 for t in range(T+1)] for robot in robots] for room in range(0, rooms+1)]
    # print(rooms)
    holding_obj = [[[Bool('taskID'+str(task.id)+'_timeStep'+str(t)+'_robotID'+str(robot.id))
                     for task in tasks] for robot in robots] for t in range(T+1)]
    # print(holding_obj)

    # Add Constraints
    s = Solver()

    # Robots start in their assigned rooms
    for robot in robots:
        s.add(b_rooms[robot.start][robot.id][0])

    # Each object is being held at some point
    for task in tasks:
        s.add(Or([holding_obj[t][robot.id][task.id]
              for robot in robots for t in range(T)]))

    # Each object is not being held at the end
    for row in holding_obj[-1][:][:]:
        for var in row:
            s.add(Not(var))

    # An agent is only ever in one room
    for t in range(T+1):
        for robot in robots:
            # An agent picks a location for each time step
            s.add(Or([b_rooms[room][robot.id][t] for room in range(rooms+1)]))

            for room1 in range(0, rooms+1):
                for room2 in range(room1+1, rooms+1):
                    # An agent cannot pick two locations at once
                    s.add(
                        Not(And(b_rooms[room1][robot.id][t], b_rooms[room2][robot.id][t])))

    # Encode the distances given by the edges
    for t in range(T+1):
        for edge in weighted_edges:
            for tau in range(t+1, min(T, t+edge.weight-1)+1):
                for robot in robots:
                    # Assuming undirected edges
                    s.add(Implies(b_rooms[edge.start][robot.id][t], Not(
                        b_rooms[edge.end][robot.id][tau])))
                    s.add(Implies(b_rooms[edge.end][robot.id][t], Not(
                        b_rooms[edge.start][robot.id][tau])))

    # Rules of holding an object
    # Holding at the start means an agent is in the room with the object
    for robot in robots:
        for task in tasks:
            s.add(Implies(holding_obj[0][robot.id]
                  [task.id], b_rooms[task.start][robot.id][0]))

    for robot in robots:
        for task in tasks:
            s.add(Implies(holding_obj[0][robot.id][task.id], Or(
                holding_obj[1][robot.id][task.id], b_rooms[task.end][robot.id][1])))
            for t in range(1, T):
                # Holding now means the agent will still be holding in the next step or dropped the item off
                s.add(Implies(holding_obj[t][robot.id][task.id], Or(
                    holding_obj[t+1][robot.id][task.id], b_rooms[task.end][robot.id][t+1])))

                # Holding now means the agent was holding last time step or is picking up the item
                s.add(Implies(holding_obj[t][robot.id][task.id], Or(
                    holding_obj[t-1][robot.id][task.id], b_rooms[task.start][robot.id][t])))
            s.add(Implies(holding_obj[T][robot.id][task.id], Or(
                holding_obj[T-1][robot.id][task.id], b_rooms[task.end][robot.id][T])))

    # Capacity Constraint
    for t in range(T+1):
        trigger = True
        for robot in robots:
            s.add(Sum([If(holding_obj[t][robot.id][task.id], 1, 0)
                  for task in tasks]) <= capacity)

    set_option(timeout=600000)
    start = time.time()
    result = s.check()
    total_time = time.time() - start
    print(f"Result : {result}")
    print(f"Seconds to solve: {total_time}")
    # """
    solverList = []
    if result == sat:
        m = s.model()

        for d in m.decls():
            line = f"{d.name()} = {m[d]}"
            # print("LINE:")
            # print(line)
            solverList.append(line)

    return solverList