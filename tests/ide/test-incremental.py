# A script to test F* interactive mode's incremental capabilities

import os
import sys
import subprocess
import json
import re
import hashlib


# The path to the F* executable
fstar = sys.argv[1]
# The file to test
file = sys.argv[2]

# approximating a test to decide if a string is an F* comment
# some ulib files have trailing comments in a variety of styles
def is_comment(str):
    if (str.startswith("(*") and str.endswith("*)")):
        return True
    lines = str.splitlines()
    for line in lines:
        line = line.strip()
        if not line: # empty lines
            continue
        if (line.startswith("(*") and line.endswith("*)")):
            continue
        if not line.startswith("//"):
            return False
    return True

def get_contents_in_range(file_lines, start_pos, end_pos):
    start_line = start_pos[0]
    start_col = start_pos[1]
    lines = []
    if (end_pos == None):
        lines.append(file_lines[start_line - 1][start_col:])
        lines.extend(file_lines[start_line:])
        lines = "\n".join(lines)
        return lines
    end_line = end_pos[0]
    end_col = end_pos[1]
    # Skip the prefix of file_lines until start_line
    # take all the lines between start_line and end_line
    if (start_line < end_line):
        lines.append(file_lines[start_line - 1][start_col:])
        lines.extend(file_lines[start_line:end_line - 1])
        lines.append(file_lines[end_line - 1][:end_col])
    elif (start_line == end_line):
        lines.append(file_lines[start_line - 1][start_col:end_col])
    # print (f"lines = {lines}")
    lines = "\n".join(lines)
    return lines

def check_one_fragment(file_lines, json_objects, from_line):
    l = from_line
    # The line from_line is the first line of the fragment
    if json_objects[l]["kind"] != "message" or json_objects[l]["level"] != "progress" or json_objects[l]["contents"]["stage"] != "full-buffer-fragment-started":
        print(f"Expected a full-buffer-fragment-started message at line {l} got {json_objects[l]}")
        return None
    l += 1
    if json_objects[l]["kind"] != "message" or json_objects[l]["level"] != "progress" or json_objects[l]["contents"]["stage"] != "full-buffer-fragment-lax-ok":
        print(f"Expected a full-buffer-fragment-lax-ok message at line {l} got {json_objects[l]}")
        return None
    lax_ok = json_objects[l]["contents"]
    code_frag = lax_ok["code-fragment"]
    start_pos = code_frag["range"]["beg"]
    end_pos = code_frag["range"]["end"]
    last_fragment_end = end_pos
    lines = get_contents_in_range(file_lines, start_pos, end_pos)
    # compute an MD5 hash of the lines
    # if the hash does not match the hash in the message, print an error message
    # and return False
    hash = hashlib.md5(lines.encode()).hexdigest()
    if hash != code_frag["code-digest"]:
        print(f"Hash does not match: Expected {hash} but got {code_frag['code-digest']}")
        return None
    # # join the lines together with newlines
    # if code_frag["code"] != lines:
    #     print(f"Code fragment does not match the code: Expected {code_frag['code']} but got {lines}")
    #     return None
    l += 1
    # Next line has the form {"kind":"response","query-id":"2.91","status":"success","response":[]}
    if json_objects[l]["kind"] != "response":
        return None
    if json_objects[l]["status"] != "success":
        return None
    l += 1
    # Next several lines have status "success" and kind=response
    while (l < len(json_objects)):
        # print(f"Checking line {l} contents {json_objects[l]}")
        # if the line has a status field
        if json_objects[l]["kind"] != "response":
            break
        if json_objects[l]["status"] != "success":
            print(f"Expected a success response at line {l} got {json_objects[l]}")
            return None
        l += 1
    return (l, last_fragment_end)

# A function to validate the response from F* interactive mode
def validate_response(response, file_contents):
    file_lines = file_contents.splitlines()
    # print(f"Validating response")
    # print(f"Response: {response}")
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
    l = 0
    # Check that the first line is a protocol-info message
    if json_objects[l]["kind"] != "protocol-info":
        print(f"Line {l} is not a protocol-info message")
        return False
    l = 1
    # Second line has kind "response" and query-id "1" and status "success"
    if json_objects[l]["kind"] != "response":
        print(f"Line {l} is not a response message")
        return False
    if json_objects[l]["query-id"] != "1":
        print(f"Line {l} does not have query-id 1")
        return False
    if json_objects[l]["status"] != "success":
        print(f"Line {l} does not have status success")
        return False

    l = 2
    if json_objects[l]["level"] != "progress" or json_objects[l]["contents"]["stage"] != "full-buffer-started":
        print(f"Line {l} is not a message: got {json_objects[l]}")
        return False
    
    l=3
    # Third line has the form {"kind":"message","query-id":"2","level":"info","contents":"Parsed 138 declarations\n"}
    if json_objects[l]["kind"] != "message":
        print(f"Line {l} is not a message {json_objects[l]}")
        return False
    if json_objects[l]["query-id"] != "2":
        print(f"Line {l} does not have query-id 2")
        return False
    if json_objects[l]["level"] != "info":
        print(f"Line {l} does not have level info")
        return False
    # the contents should match a regular expression of the form "Parsed \d+ declarations"
    # store the number of declarations in a variable
    if not re.match(r"Parsed \d+ declarations", json_objects[l]["contents"]):
        print(f"Line {l} does not have the correct contents")
        return False
    # Check that the number of declarations is 138
    num_decls = int(re.search(r"\d+", json_objects[l]["contents"]).group())
    l=4
    # Fourth line has kind "message" and level "progress" and contents.stage = "full-buffer-fragment-started"
    if json_objects[l]["kind"] != "message":
        print(f"Line {l} is not a message; got {json_objects[l]}")
        return False
    if json_objects[l]["level"] != "progress":
        print(f"Line {l} does not have level progress; got {json_objects[l]}")
        return False
    if json_objects[l]["contents"]["stage"] != "full-buffer-fragment-started":
        print(f"Line {l} does not have stage full-buffer-fragment-started; got {json_objects[l]}")
        return False
    i = 5
    # With fly_deps (the default), there are no loading-dependency messages.
    # Without fly_deps, next several messages are progress messages with
    # contents.stage = "loading-dependency", followed by a stage=None sentinel.
    # Handle both cases.
    while (i < len(json_objects) - 1
           and json_objects[i]["kind"] == "message"
           and json_objects[i]["level"] == "progress"
           and json_objects[i]["contents"]["stage"] == "loading-dependency"):
        i += 1
    # If we saw any loading-dependency messages, the next message has stage=None
    if i > 5:
        if json_objects[i]["contents"]["stage"] != None:
            print(f"Message {i} has contents {json_objects[i]} does not have stage None")
            return False
        i += 1
    # the next message has contents.stage = "full-buffer-fragment-lax-ok"
    if json_objects[i]["contents"]["stage"] != "full-buffer-fragment-lax-ok":
        print("Message does not have stage full-buffer-fragment-lax-ok")
        return False
    i += 1
    if json_objects[i]["status"] != "success":
        print(f"Message does not have success message at line {i}")
        return False
    i += 1
    # Then, we have a sequence of fragments, each handled by check_one_fragment
    num_successes = 1
    last_fragment_end = [0, 0]
    while (i < len(json_objects) - 1):
        if json_objects[i]["kind"] != "message":
            break
        if json_objects[i]["level"] != "progress":
            break
        if json_objects[i]["contents"]["stage"] != "full-buffer-fragment-started":
            break
        res = check_one_fragment(file_lines, json_objects, i)
        if res == None:
            return False
        (i, last_fragment_end) = res
        num_successes += 1
    remaining_lines = get_contents_in_range(file_lines, last_fragment_end, None)
    remaining_lines = remaining_lines.strip()
    if remaining_lines != "" and not (is_comment(remaining_lines)):
        print(f"Remaining lines are not empty: {remaining_lines}")
        return False
    if num_successes != num_decls:
        print(f"Number of successes {num_successes} does not match number of declarations {num_decls}")
        return False
    
    # check that i is the index of the secod last message
    if i != len(json_objects) - 2:
        print(f"Unexpected last message at index {i}, contents = {json_objects[i]}")
        return False
    if json_objects[i]["kind"] != "message" or json_objects[i]["level"] != "progress" or json_objects[i]["contents"]["stage"] != "full-buffer-finished":
        print(f"Unexpected last message at index {i}, contents = {json_objects[i]}")
        return False
    i += 1
    # The last message has query-id "3" and status "success"
    if json_objects[i]["query-id"] != "3":
        print("Last message does not have query-id 3")
        return False
    
    return True

# A function to test fstar on a single file
def test_file(filepath):
    # prepend the path ../../ulib to the file
    print(f"Testing {filepath}")
    # flush stdout
    sys.stdout.flush()
    with open(filepath, "r") as f:
        contents = f.read()
    # Escape the contents of the file for JSON
    json_contents = json.dumps(contents)
    # print(contents)
    # Format the contents of the file into a request for the F* ide
    # The first line is a JSON object initializing the ide
    # The second line is a JSON object containing the contents of the file
    # The third line is an exit command
    request = f'{{"query-id":"1", "query": "vfs-add", "args":{{"filename":null, "contents": {json_contents}}}}}\n{{"query-id":"2", "query": "full-buffer", "args":{{"kind": "lax", "with-symbols":true, "code": {json_contents}, "line":1, "column":0}}}}\n{{"query-id":"3", "query": "exit", "args":{{}}}}\n'
    # print the request to the console for debugging
    # print(request)
    # Run fstar on the file with the request as stdin
    p = subprocess.run([fstar, "--admit_smt_queries", "true", "--ide", file], input=request, encoding="utf-8", stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    # Read the response from stdout
    response = p.stdout
    # Print the response to the console for debugging
    #print(response)
    # Check that fstar exited with code 0
    if p.returncode != 0:
        print("F* returned non-zero exit code")
        print(p.stderr)
        print(p.stdout)
        return False
    # Parse the response into a list of lines
    # lines = response.splitlines()
    # Print the number of lines in the response
    # print(f"Response: {response}")
    # Validate the response
    return validate_response(response, contents)

if test_file(file):
    print(f"OK {file}")
    sys.exit(0)
else:
    print(f"Testing {file} FAILED")
    sys.exit(1)
