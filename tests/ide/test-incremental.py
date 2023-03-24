# A script to test F* interactive mode's incremental capabilities

import os
import sys
import subprocess
import json
import re


# The path to the F* executable
fstar = sys.argv[1]

# A function to validate the response from F* interactive mode
def validate_response(response):
    # parse the each line of the response into a JSON object
    # if the line is not valid JSON, print an error message and exit
    # store the JSON objects in a list
    json_objects = []
    for line in response.splitlines():
        try:
            resp = json.loads(line)
            json_objects.append(resp)
        except json.JSONDecodeError:
            print(f"Invalid JSON: {line}")
            return False
    # Check that the first line is a protocol-info message
    if json_objects[0]["kind"] != "protocol-info":
        print("First line is not a protocol-info message")
        return False
    # Second line has kind "response" and query-id "1" and status "success"
    if json_objects[1]["kind"] != "response":
        print("Second line is not a response message")
        return False
    if json_objects[1]["query-id"] != "1":
        print("Second line does not have query-id 1")
        return False
    if json_objects[1]["status"] != "success":
        print("Second line does not have status success")
        return False
  
    # Third line has the form {"kind":"message","query-id":"2","level":"info","contents":"Parsed 138 declarations\n"}
    if json_objects[2]["kind"] != "message":
        print(f"Second line is not a message {json_objects[2]}")
        return False
    if json_objects[2]["query-id"] != "2":
        print("Second line does not have query-id 2")
        return False
    if json_objects[2]["level"] != "info":
        print("Second line does not have level info")
        return False
    # the contents should match a regular expression of the form "Parsed \d+ declarations"
    # store the number of declarations in a variable
    if not re.match(r"Parsed \d+ declarations", json_objects[2]["contents"]):
        print("Second line does not have the correct contents")
        return False
    # Check that the number of declarations is 138
    num_decls = int(re.search(r"\d+", json_objects[2]["contents"]).group())
 
    # Fourth line has kind "message" and level "progress" and contents.stage = "full-buffer-fragment-started"
    if json_objects[3]["kind"] != "message":
        print("Third line is not a message")
        return False
    if json_objects[3]["level"] != "progress":
        print("Third line does not have level progress")
        return False
    if json_objects[3]["contents"]["stage"] != "full-buffer-fragment-started":
        print("Third line does not have stage full-buffer-fragment-started")
        return False

    # Next several messages are progress messages with contents.stage = "loading-dependency"
    # Check all of these messages for the correct kind, level, and stage and stop
    # when the first message with a different kind or level or stage is found
    for i in range(4, len(json_objects) - 1):
        if json_objects[i]["kind"] != "message":
            break
        if json_objects[i]["level"] != "progress":
            break
        if json_objects[i]["contents"]["stage"] != "loading-dependency":
            break
    # the message and index i has contents.stage = None
    if json_objects[i]["contents"]["stage"] != None:
        print(f"Message {i} has contents {json_objects[i]} does not have stage None")
        return False
    # the next message has conents.stage = "full-buffer-fragment-lax-ok"
    if json_objects[i + 1]["contents"]["stage"] != "full-buffer-fragment-lax-ok":
        print("Message does not have stage full-buffer-fragment-lax-ok")
        return False
    # Then, we have a sequence of pairs of messages
    # where the first message in the pair has contents.stage = "full-buffer-fragment-started"
    # and the second message in the pair has contents.stage = "full-buffer-fragment-lax-ok"
    # Check all of these messages for the correct kind, level, and stage and stop
    # when the first message with a different kind or level or stage is found
    # The first message in the pair has contents.stage = "full-buffer-fragment-started"
    # The second message in the pair has contents.stage = "full-buffer-fragment-lax-ok"
    num_successes = 1
    for j in range(i + 2, len(json_objects) - 1, 2):
        if json_objects[j]["kind"] != "message":
            break
        if json_objects[j]["level"] != "progress":
            break
        if json_objects[j]["contents"]["stage"] != "full-buffer-fragment-started":
            break
        if json_objects[j + 1]["contents"]["stage"] != "full-buffer-fragment-lax-ok":
            break
        num_successes = num_successes + 1

    if num_successes != num_decls:
        print(f"Number of successes {num_successes} does not match number of declarations {num_decls}")
        return False
    
    # The next sequence of messages have status success and query-id "2"
    # Check all of these messages for the correct kind and status and stop
    # when the first message with a different kind or status is found
    for k in range(j + 1, len(json_objects)):
        if json_objects[k]["kind"] != "response":
            break
        if json_objects[k]["status"] != "success":
            break
        if json_objects[k]["query-id"] != "2":
            break

    # check that k is the index of the last message
    if k != len(json_objects) - 1:
        print(f"Unexpected last message at index {k}, contents = {json_objects[k]}")
        return False

    # The last message has query-id "3" and status "success"
    if json_objects[k]["query-id"] != "3":
        print("Last message does not have query-id 3")
        return False
    
    return True

# A function to test fstar on a single file
def test_file(file):
    # prepend the path ../../ulib to the file
    filepath = os.path.join("../../ulib", file)
    print(f"Testing {filepath}")
    # flush stdout
    sys.stdout.flush()
    with open(filepath, "r") as f:
        contents = f.read()
    # Escape the contents of the file for JSON
    contents = json.dumps(contents)
    # print(contents)
    # Format the contents of the file into a request for the F* ide
    # The first line is a JSON object initializing the ide
    # The second line is a JSON object containing the contents of the file
    # The third line is an exit command
    request = f'{{"query-id":"1", "query": "vfs-add", "args":{{"filename":null, "contents": {contents}}}}}\n{{"query-id":"2", "query": "full-buffer", "args":{{"kind": "full-with-symbols", "code": {contents}, "line":1, "column":0}}}}\n{{"query-id":"3", "query": "exit", "args":{{}}}}\n'
    # print the request to the console for debugging
    #print(request)
    # Run fstar on the file with the request as stdin
    p = subprocess.run([fstar, "--admit_smt_queries", "true", "--ide", file], input=request, encoding="utf-8", stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    # Read the response from stdout
    response = p.stdout
    # Print the response to the console for debugging
    # print(response)
    # Check that fstar exited with code 0
    if p.returncode != 0:
        print("F* returned non-zero exit code")
        print(p.stderr.read())
        print(p.stdout.read())
        return False
    # Parse the response into a list of lines
    lines = response.splitlines()
    # Print the number of lines in the response
    #print(f"Response has {len(lines)} lines")
    # Validate the response
    return validate_response(response)

# List all files in ../../ulib
files = os.listdir("../../ulib")
# Filter the list to only include .fst and .fsti files
files = [f for f in files if f.endswith(".fst") or f.endswith(".fsti")]
succeeded = True
# For each file files, test fstar on the file
for file in files:
    # If the test fails, exit with code 1
    if not test_file(file):
        print(f"Failed test on {file}")
        succeeded = False

if succeeded:
    print("All tests passed")
    sys.exit(0)
else:
    print("Some tests failed")
    sys.exit(1)