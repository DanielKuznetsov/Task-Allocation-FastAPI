from fastapi import FastAPI, HTTPException
from fastapi.middleware.cors import CORSMiddleware
from mangum import Mangum
from pydantic import BaseModel
from uuid import uuid4
from typing import Optional, List
from z3 import *
import time

app = FastAPI()

handler = Mangum(app)

# Configure CORS
app.add_middleware(
    CORSMiddleware,
    allow_origins=["*"],  
    allow_credentials=True,
    allow_methods=["*"],   
    allow_headers=["*"],  
)

class WeightedEdge:
    def __init__(self, start, end, weight) -> None:
        self.start = start
        self.end = end
        self.weight = weight
        assert isinstance(self.weight, int)

class Task:
    def __init__(self, id, start, end) -> None:
        self.id = id
        self.start = start
        self.end = end

    def __str__(self):
        return f"{self.id}: {self.start} -> {self.end}"

class Robot:
    def __init__(self, id, start) -> None:
        self.id = id
        self.start = start

class RobotState:
    def __init__(self, robot_id, location):
        self.robot_id = robot_id
        self.location = location

class TaskState:
    def __init__(self, task_id, location):
        self.task_id = task_id
        self.location = location

class SolveTask(BaseModel):
    startRoom: str
    endRoom: str
    task_ID: str

class SolveRobot(BaseModel):
    startRoom: str
    robot_ID: str

class SolveRequest(BaseModel):
    tasks: List[SolveTask]
    robots: List[SolveRobot]
    max_time: int

class ValidateRequest(BaseModel):
    tasks: List[SolveTask]
    robots: List[SolveRobot]

@app.get("/")
async def root():
    return {"message": "Hello World from the API!"}

@app.post("/validate")
async def validate(validate_request: ValidateRequest):
    tasks = validate_request.tasks
    robots = validate_request.robots

    TASKS = []
    for task in tasks:
        task_id = int(task.task_ID)
        start_room = int(task.startRoom)
        end_room = int(task.endRoom)

        new_task = Task(task_id, start_room, end_room)

        TASKS.append(new_task)

    ROBOTS = []
    for robot in robots:
        robot_id = int(robot.robot_ID)
        start_room = int(robot.startRoom)

        new_robot = Robot(robot_id, start_room)

        ROBOTS.append(new_robot)

    ROOMS = 7
    CAPACITY = 1
    WEIGHTED_EDGES = [
        WeightedEdge(1, 2, 2), WeightedEdge(1, 3, 1), WeightedEdge(1, 4, 2),
        WeightedEdge(1, 5, 2), WeightedEdge(1, 6, 4), WeightedEdge(1, 7, 6),
        WeightedEdge(2, 3, 3), WeightedEdge(2, 4, 2), WeightedEdge(2, 5, 4),
        WeightedEdge(2, 6, 2), WeightedEdge(2, 7, 4), WeightedEdge(3, 4, 3),
        WeightedEdge(3, 5, 1), WeightedEdge(3, 6, 5), WeightedEdge(3, 7, 8),
        WeightedEdge(4, 5, 4), WeightedEdge(4, 6, 4), WeightedEdge(4, 7, 6),
        WeightedEdge(5, 6, 6), WeightedEdge(5, 7, 8), WeightedEdge(6, 7, 4),
    ]

    projectedTime = 1
    terminateFlag = False

    while not terminateFlag:
        isSat = validate_solver(ROBOTS, TASKS, ROOMS,
                                WEIGHTED_EDGES, projectedTime, CAPACITY)
                
        if isSat != unsat:
            terminateFlag = True
            return projectedTime
        else:
            projectedTime += 1

@app.post("/solve")
async def solve(solve_request: SolveRequest):
    tasks = solve_request.tasks
    robots = solve_request.robots
    max_time = solve_request.max_time

    TASKS = []
    for task in tasks:
        task_id = int(task.task_ID)
        start_room = int(task.startRoom)
        end_room = int(task.endRoom)

        new_task = Task(task_id, start_room, end_room)
        
        print("Task: ", new_task.id, "Start: ", new_task.start, "End: ", new_task.end)

        TASKS.append(new_task)

    ROBOTS = []
    for robot in robots:
        robot_id = int(robot.robot_ID)
        start_room = int(robot.startRoom)

        new_robot = Robot(robot_id, start_room)
        
        print("Robot: ", new_robot.id, "Start: ", new_robot.start)

        ROBOTS.append(new_robot)

    ROOMS = 7
    CAPACITY = 1
    WEIGHTED_EDGES = [
        WeightedEdge(1, 2, 2), WeightedEdge(1, 3, 1), WeightedEdge(1, 4, 2),
        WeightedEdge(1, 5, 2), WeightedEdge(1, 6, 4), WeightedEdge(1, 7, 6),
        WeightedEdge(2, 3, 3), WeightedEdge(2, 4, 2), WeightedEdge(2, 5, 4),
        WeightedEdge(2, 6, 2), WeightedEdge(2, 7, 4), WeightedEdge(3, 4, 3),
        WeightedEdge(3, 5, 1), WeightedEdge(3, 6, 5), WeightedEdge(3, 7, 8),
        WeightedEdge(4, 5, 4), WeightedEdge(4, 6, 4), WeightedEdge(4, 7, 6),
        WeightedEdge(5, 6, 6), WeightedEdge(5, 7, 8), WeightedEdge(6, 7, 4),
    ]
    SET_T = max_time
    solverList = create_solver(
        ROBOTS, TASKS, ROOMS, WEIGHTED_EDGES, SET_T, CAPACITY)

    backend = {
        "tasksLocations": {},
        "timeline": {},
        "whoCarriesWhat": {}
    }

    def extract_timeStep(line):
        parts = line.split("_")
        timeStepStr = parts[1].replace("timeStep", "")
        return int(timeStepStr)

    sortedLines = sorted(solverList, key=extract_timeStep)
    filteredLines = []

    for line in sortedLines:
        newLine = line.strip("\n").strip(" ")

        if newLine.startswith("task") and newLine.endswith("True"):
            filteredLines.append(newLine)
        elif newLine.startswith("robot") and newLine.endswith("True"):
            filteredLines.append(newLine)

    def parse_line(line, allLines):
        parts = line.split("_")
        timeStep = int(parts[1].replace("timeStep", ""))
        entityType = None
        taskRoom = None
        status = None

        if parts[0].startswith("robot"):
            entityType = "robots"
        elif parts[0].startswith("task"):
            entityType = "tasks"
        else:
            print("ERROR: unknown entity type")

        entityID = parts[0].replace("robotID", "").replace("taskID", "")

        room = None
        robotID = None

        if entityType == "robots":
            room = int(parts[2].split(" = ")[0].replace("room", ""))
        # status = line.split(" = ")[1].strip()

        if entityType == "tasks":
            robotID = int(parts[2].split(" = ")[0].replace("robotID", ""))
            status = parts[2].split(" = ")[1]

            for eachLine in allLines:
                newLine = eachLine.strip("\n").strip(" ")

                if newLine.startswith("robot") and newLine.endswith("True"):
                    lineParts = newLine.split("_")
                    lineRobotID = lineParts[0].replace("robotID", "")
                    lineTimeStep = lineParts[1].replace("timeStep", "")

                    if lineRobotID == str(robotID) and lineTimeStep == str(timeStep):
                        lineRoomPart = lineParts[2].split(" = ")[0]
                        taskRoom = int(lineRoomPart.replace("room", ""))

                        # print(f"parse_line - Task {entityID}, TimeStep: {timeStep}, Task Room Set to: {taskRoom} based on line: {newLine}")
                        break

        return timeStep, entityType, entityID, room, robotID, taskRoom, status

    tasks = {}

    for line in filteredLines:
        newLine = line.strip("\n").strip(" ")

        if newLine.startswith("robot") and newLine.endswith("True"):
            timeStep, entityType, entityID, room, robotID, taskRoom, status = parse_line(
                newLine, sortedLines)

            if timeStep not in backend["timeline"]:
                backend["timeline"][timeStep] = {"robotsLocations": {}}

            backend["timeline"][timeStep]["robotsLocations"][entityID] = {
                "id": entityID,
                "room": room,
                "status": ""
            }

        if newLine.startswith("task"):
            timeStep, entityType, entityID, room, robotID, taskRoom, status = parse_line(
                newLine, sortedLines)

            if status == "True":
                if entityID not in backend["tasksLocations"]:
                    # print("PICK UP TIME: ", timeStep)
                    backend["tasksLocations"][entityID] = {
                        "id": entityID,
                        "robotDeployed": robotID,
                        "pickUpRoom": taskRoom,
                        "pickUpTime": timeStep,
                        "dropOffRoom": None,
                        "dropOffTime": None,
                    }

                    if robotID not in backend["whoCarriesWhat"]:
                        backend["whoCarriesWhat"][robotID] = [entityID]
                    else:
                        backend["whoCarriesWhat"][robotID].append(entityID)

                tasks[entityID] = {"timeStep": timeStep, "robotID": robotID}

    for entityID, info in tasks.items():
        drop_off_time = info["timeStep"] + 1
        backend["tasksLocations"][entityID]["dropOffTime"] = drop_off_time

        for line in filteredLines:
            newLine = line.strip("\n").strip(" ")

            if newLine.startswith("robot") and newLine.endswith("True"):
                lineParts = newLine.split("_")
                lineRobotID = lineParts[0].replace("robotID", "")
                lineTimeStep = lineParts[1].replace("timeStep", "")

                if lineRobotID == str(info["robotID"]) and lineTimeStep == str(drop_off_time):
                    lineRoomPart = lineParts[2].split(" = ")[0]
                    taskRoom = int(lineRoomPart.replace("room", ""))

                    backend["tasksLocations"][entityID]["dropOffRoom"] = taskRoom

                    break

    last_time_step = max(backend["timeline"].keys())

    for timeStep, robots in backend["timeline"].items():
        robot_location = robots["robotsLocations"][robot_id]

        if timeStep == 0:
            robot_location["status"] = "idle"

        current_room = robot_location["room"]
        task = backend["tasksLocations"][robot_id]  # Assuming this is how you get the task for the robot

        # Check if the robot is at the pick-up or drop-off room at the correct time
        if timeStep == task["pickUpTime"] and current_room == task["pickUpRoom"]:
            robot_location["status"] = "picked up"
        elif timeStep == task["dropOffTime"] and current_room == task["dropOffRoom"]:
            robot_location["status"] = "dropped off"
        else:
            # For other time steps, check if the robot has reached its destination
            if task["pickUpTime"] < timeStep <= task["dropOffTime"]:
                robot_location["status"] = "carrying task"
            else:
                robot_location["status"] = "en route"

        if timeStep == last_time_step and robot_location["status"] == "dropped off":
            robot_location["status"] = "completed"

        if previous_room is not None and previous_room != current_room:
            same_room = False
        previous_room = current_room

        if same_room:
            backend["timeline"][last_time_step]["robotsLocations"][robot_id]["status"] = "completed"

    return backend

def validate_solver(robots, tasks, rooms, weighted_edges, T, capacity=1):
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
    return result

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

@app.get("/z3version")
def z3_version():
    return {"z3_version": z3.get_version_string()}