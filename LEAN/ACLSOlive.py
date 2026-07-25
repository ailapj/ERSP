import subprocess
import os
import re
from dotenv import load_dotenv
from anthropic import Anthropic
import threading 

load_dotenv()
load_dotenv(override=True)
client = Anthropic(api_key=os.getenv("ANTHROPIC_API_KEY"))


IMPORT_LINE = "import Tutorial.Lean.ACLS"
CANDIDATE_PATH = "candidate.lean"
REFERENCE_PATH = "Tutorial/Lean/ACLS.lean"
with open(REFERENCE_PATH, "r", encoding="utf-8") as reference_spec:
            REFERENCE_SPEC = reference_spec.read()
with open(CANDIDATE_PATH, "r", encoding="utf-8") as candidate_plan:
            CANDIDATE_PLAN = candidate_plan.read()


# Timer manager
class TimerManager:
    def __init__(self):
        self.active = {}

    def start(self, name, seconds):
        # Don't start another timer if one is already running
        if name in self.active:
            return

        def expired():
            print(f"\n[TIMER] {name} expired!")

            # remove timer from active list
            self.active.pop(name, None)

        timer = threading.Timer(seconds, expired)

        self.active[name] = timer
        timer.start()

        print(f"[TIMER] Started {name} ({seconds} seconds)")

timers = TimerManager()

class ConversationState:
    def __init__(self):
        self.history = []          # natural language dialogue
        self.current_lean = CANDIDATE_PLAN # latest verified Lean program
        # self.turn = 0, possibly uncomment if different behaivor is needed for longer convos. 

def add_message(state, message, role):
    state.history.append({
        "role": role, 
        "content": message
    })
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

# # determining what the latest event was to trigger timer if appropriate
# def timer_trigger():
#     eval_file = "candidate_eval.lean"

#     with open(CANDIDATE_PATH, "r", encoding="utf-8") as f:
#         candidate_code = f.read()

#     eval_code = candidate_code + """
# #eval user.timers
# """

#     with open(eval_file, "w", encoding="utf-8") as f:
#         f.write(eval_code)

#     returncode, stdout, stderr = run_lean(eval_file)

#     if returncode != 0:
#         print("Lean evaluation failed:")
#         print(stderr)
#         return None

#     matches = re.findall(
#         r"duration\s*:=\s*(\d+)\s*,\s*type\s*:=\s*TimerKind\.(\w+)",
#         stdout,
#     )

#     for duration, timer_name in matches:
#         duration = int(duration)
#         timers.start(timer_name, duration)

#     return stdout

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
def generate_plan(state):

    conversation = "\n".join(
        f"{m['role']}: {m['content']}"
        for m in state.history
    )
    prompt = f"""
conversation so far: 
{conversation}

lean specficiation: 
{REFERENCE_SPEC}

Previously verified Lean state:
{state.current_lean}

RULES: 
- The above Lean specification is immutable and encodes the official procedure to be followed.
- You may only use definitions from this specification.
- For every patient field you fill, there must be clear indication of it from the user. 
- Preserve every previously verified fact unless the user's new information explicitly contradicts it.
- Output ONLY Lean code enclosed in a ```lean``` block. 
"""

    return call_claude(prompt, temperature=0)


# The full pipeline of generating the initial plan, repairing syntax errors , then repairing logic errors if the generated plan is not safe
def generate_and_verify(state):
    for i in range(1):
        print(f"\n == Pipleline round {i+1} ==")

        # generate plan
        generated_response = generate_plan(state)
        save_file(generated_response, CANDIDATE_PATH) 

        # logic phase
        if repair_loop():
            with open(CANDIDATE_PATH, "r", encoding="utf-8") as f:
                state.current_lean = f.read()
            return True

    return False

def natural_language(state):
    conversation = "\n".join(
        f"{m['role']}: {m['content']}"
        for m in state.history
    )

    _, stdout, stderr = run_lean(CANDIDATE_PATH)

    prompt = f"""
Conversation 
{conversation}

Verified Lean Program 
{state.current_lean}

Here is the stdout and stderr of the lean program: 
{stdout}, {stderr}

Simply translate these to natural human language. 

If needed, ask a clarifying follow-up question that either leads the conversation forward, will most reduce the any uncertainity about patient's status or user inquiry, or allows the user to make corrections. 
 """
    
    return call_claude(prompt, temperature=0.7)

def chat():
    state = ConversationState()

    while True:

        user = input("\nUser: ")

        if user.lower() in {"quit", "exit"}:
            break

        add_message(state, user, "user")

        success = generate_and_verify(state)

        if not success:
            print("Failed to produce safe plan")
            continue

        reply = natural_language(state)

        add_message(state, reply, "assistant")

        print("\nAssistant:")
        print(reply)
    print (state.history)
# ------------------ Main ------------------
def main():
    print("Enter scenario:\n> ")
    chat()

if __name__ == "__main__":
    main()