import subprocess
import os
import re
from dotenv import load_dotenv
from anthropic import Anthropic
import threading 
from queue import Queue

load_dotenv()
load_dotenv(override=True)
client = Anthropic(api_key=os.getenv("ANTHROPIC_API_KEY"))

event_queue = Queue()

IMPORT_LINE = "import Tutorial.Lean.ACLS"
CANDIDATE_PATH = "candidate.lean"
REFERENCE_PATH = "Tutorial/Lean/ACLS.lean"
BASE_PATH = "base.txt"
with open(REFERENCE_PATH, "r", encoding="utf-8") as reference_spec:
            REFERENCE_SPEC = reference_spec.read()
with open(CANDIDATE_PATH, "r", encoding="utf-8") as candidate_plan:
            CANDIDATE_PLAN = candidate_plan.read()
event_history = []

class ConversationState:
    def __init__(self):
        self.history = []          # natural language dialogue
        self.current_lean = CANDIDATE_PLAN # latest verified Lean program
        # self.turn = 0, possibly uncomment if different behaivor is needed for longer convos. 

state = ConversationState()

# Timer manager
class TimerManager:
    def __init__(self):
        self.active = {}

    def start(self, name, seconds):
        # Don't start another timer if one is already running
        if name in self.active:
            return

        def expired():
            message = f"{name} for {seconds} seconds expired."
            add_message(message, "TIMER")
            print(f"\n[TIMER] {name} expired!")

            # remove timer from active list
            self.active.pop(name, None)

        timer = threading.Timer(seconds, expired)

        self.active[name] = timer
        timer.start()
        message = f"{name} for {seconds} seconds started."
        add_message(message, "TIMER", trigger_pipeline=False)

        print(f"[TIMER] Started {name} ({seconds} seconds)")

timers = TimerManager()


def add_message(message, role, trigger_pipeline=True):
    state.history.append({
        "role": role,
        "content": message
    })

    if trigger_pipeline:
        event_queue.put(role)

# Calling Claude with the prompt 
def call_claude(prompt, max_new_tokens=4000, temperature=0.7):
    message = client.messages.create(
        model="claude-opus-4-6",
        max_tokens=max_new_tokens, # how long the response can be (one token is roughly 4 characters, so 200 tokens is about 800 characters)
        temperature=temperature, # randomness (0 = deterministic, higher temperature = more random)
        # caching the reference spec that never changes-- it does not work right now because caching content is too small (?)
        system=[
            {
                "type":"text",
                "text" : REFERENCE_SPEC, 
                "cache_control" : {"type": "ephemeral"}, 
            }
        ], 
        messages=[
            {"role": "user", "content": prompt}
        ],
    )
    # writing the claude outputs in log.txt to keep track
    with open("ai_log.txt", "a", encoding="utf-8") as f:
        f.write(message.content[0].text + "\n\n" + "="*60 + "\n\n")
    return message.content[0].text

# Extract only the lean code from the generated response  
def extract_lean_code(response_text):
    # searches for the '''lean ''' 
    match = re.search(
        r"```(?:lean)?\s*\n(.*?)```",
        response_text,
        re.DOTALL | re.IGNORECASE,
    )
    if match:
        return match.group(1).strip()
    return response_text.strip()

# Ensures that the given proof is not trivial (true if sound, false if too simple)
def sound_proof(response_text) -> bool:
    # make sure the given proof does not contain forbidden words 
    forbidden = [
        r"\bsorry\b",
        r"\badmit\b",
        r"\bstructure\b", # might delete later, for now so that the LLM does not make it's own procedures 
    ]
    pattern = r"\b(" + "|".join(forbidden) + r")\b"
    return re.search(pattern, response_text) is None  


# Ensuring that the correct import line is at the top of every saved candidate.lean file 
def ensure_import(content: str) -> str:
    lines = content.splitlines()
    first_nonempty = next((line.strip() for line in lines if line.strip()), "") 
    if first_nonempty == IMPORT_LINE:
         return content 
    return IMPORT_LINE + "\n\n" + content.lstrip()

# Save the argument content to a file at the specified path and return the path.
def save_file(content: str, file_path: str) -> str:
    content = extract_lean_code(content)
    content = ensure_import(content)

    with open(file_path, "w", encoding="utf-8") as f:
        f.write(content)

    return file_path



# Run Lean on the given file path and return a tuple of (return code, stdou, stderr).
# returncode = 0 --> success, =1 --> some error
# stdout captures: file path, errors, goal diagnostics, = null if returncode is 0 
# stderr is null if returncode is 0
def run_lean(lean_file):
    lean_file = os.path.abspath(lean_file)
    result = subprocess.run(
        ["lake", "env", "lean", lean_file],
        capture_output=True,
        text=True,
        check=False, 
    )
    return result.returncode, result.stdout, result.stderr



# determining what the latest event was to trigger timer if appropriate
def timer_trigger():
    _, stdout, _ = run_lean(CANDIDATE_PATH)

    matches = re.findall(
        r"duration\s*:=\s*(\d+)\s*,\s*type\s*:=\s*TimerKind\.(\w+)",
        stdout,
    )

    for duration, timer_name in matches:
        duration = int(duration)
        timers.start(timer_name, duration)

    return stdout

# extract the events from the llm respond and add thme to event_history
def extract_events(response):
    match = re.search(r"\[(.*?)\]", response, re.DOTALL)

    if not match:
        return []

    events = [
        e.strip()
        for e in match.group(1).split(",")
        if e.strip()
    ]

    event_history.extend(events)

    return events


# writes the events in event_history to a block of lean code 
def write_events():
    return (
        "def events : List Event := [\n    "
        + ",\n    ".join(event_history)
        + "\n]\n"
    )

# using the written block, write the entire candidate plan and save to CANDIDATE_PATH
def build_candidate(response):
    extract_events(response)
    events_block = write_events()
    with open(BASE_PATH, "r", encoding="utf-8") as f:
            base_code = f.read()
    candidate = base_code.replace("{EVENTS}", events_block)
    with open(CANDIDATE_PATH, "w", encoding="utf-8") as f:
        f.write(candidate)

# Helper function that implements a loop to repair errors and get a safe plan. 
# Also ensures that the plan is not trivially true or too simple 
def repair_loop(max_attempts=5):
    for attempt in range(max_attempts):
        print(f"\n[Repair Attempt {attempt+1}]")
        prompt = ""
        # Run the Lean code to capture the diagnostics and return values 
        returncode, stdout, stderr = run_lean(CANDIDATE_PATH)

        with open(CANDIDATE_PATH, "r", encoding="utf-8") as f:
            candidate_code = f.read()
        # Check to make sure the plan is sound and not too simple
        if not sound_proof(candidate_code) : 
            prompt += "The proof was rejected because it contains an incomplete proof placeholder.\n"
        elif returncode == 0 : 
            # capture the output 
            print("SAFE and SOUND: No violating instance exists. Exiting repair loop")
            return True

        prompt += f"""
You are repairing a Lean plan.

The theorem that the candidate plan is safe is not proven correctly. 

GOAL:
Modify the candidate plan so that the proof of its safety is provable. Then prove it. 

RULES:
- Only use variables, signatures, and fields already defined in the file below. Do NOT invent new names.
- Do not use trivially correct proofs (e.g. 'sorry') 
- Only use 'eval' and 'theorem'. do NOT use 'def'. 

Reference spec: 
The Lean specification has already been provided in the system prompt.

current code: 
{candidate_code}

Lean stdout output:
{stdout}
Lean stderr output: 
{stderr}
"""
        generated_plan = call_claude(prompt, temperature=0)
        save_file(generated_plan, CANDIDATE_PATH)

    # If we exhaust all attempts without success, return False to indicate failure.
    return False


# The first generation step where we prompt the LLM to generate a plan from scratch based on the user prompt. 
def generate_plan():

    conversation = "\n".join(
        f"{m['role']}: {m['content']}"
        for m in state.history
    )
    prompt = f"""
You are an information extraction system.

This is the immutable protocol code in Lean for reference {REFERENCE_SPEC}

Your task is ONLY to identify new events explicitly described in the user's latest message.

The previous patient state has already been verified in Lean.
Do NOT reconstruct the patient.
Do NOT infer missing information.
Do NOT repeat previous events.
Do NOT determine the next treatment.
If you are uncertain about the user statement, ask a clarifying question that leads the conversation forward

Rules:
- Only emit an event if the user's latest message explicitly supports it.
- If nothing new happened, output [].
- Multiple events may be emitted if explicitly stated.
- Never invent an event.
- Any question for the user should appear under "Questions for user" 

Output: 
1) [new Events]
2) "Questions for user" : if any 


Examples:

User:
"We started CPR."

Output:
[Event.CPRStarted]

User:
"We shocked him twice."

Output:
[Event.ShockDelivered, Event.ShockDelivered]

User:
"VF on the monitor."

Output:
[Event.RhythmObserved Rhythm.VF]

User:
"I think we should shock again."

Output:
[]

Current patient status: {run_lean(CANDIDATE_PATH)}
Current state of the conversation so far: {conversation}
"""

    return call_claude(prompt, temperature=0)


# The full pipeline of generating the initial plan, repairing syntax errors , then repairing logic errors if the generated plan is not safe
def generate_and_verify():
    for i in range(1):
        print(f"\n == Pipleline round {i+1} ==")

        # generate plan
        generated_response = generate_plan()
        build_candidate(generated_response)
        run_lean(CANDIDATE_PATH) 
        timer_trigger()

    return True

def natural_language():
    conversation = "\n".join(
        f"{m['role']}: {m['content']}"
        for m in state.history
    )

    _, stdout, _ = run_lean(CANDIDATE_PATH)

    prompt = f"""
Conversation 
{conversation}

Here is the stdout of the Lean program based on verified protocol: 
{stdout}

Simply translate the next actions to be done to natural human language. 

If needed, ask a clarifying follow-up question that either leads the conversation forward, will most reduce the any uncertainity about patient's status or user inquiry, or allows the user to make corrections. 
 """
    
    return call_claude(prompt, temperature=0.7)

def pipeline_worker():
    while True:
        event = event_queue.get()
        print(f"Processing {event} event")
        # Collapse all pending events into one update
        while not event_queue.empty():
            event_queue.get_nowait()
            event_queue.task_done()

        try:
            success = generate_and_verify()

            if success:
                reply = natural_language()

                # Don't re-enqueue assistant messages
                add_message(reply, "assistant", trigger_pipeline=False)
                print(f"\nAssistant: {reply}")

        finally:
            event_queue.task_done()

def chat():
    worker = threading.Thread(
        target=pipeline_worker,
        daemon=True
    )
    worker.start()

    while True:
        user = input("\nUser: ")
        if user.lower() in {"quit", "exit"}:
            break
        add_message(user, "user")

    print(state.history)

# ------------------ Main ------------------
def main():
    print("User Input:\n> ")
    chat()

if __name__ == "__main__":
    main()