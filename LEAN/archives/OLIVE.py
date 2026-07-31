import subprocess
import os
import re
from dotenv import load_dotenv
from anthropic import Anthropic

load_dotenv()
load_dotenv(override=True)
client = Anthropic(api_key=os.getenv("ANTHROPIC_API_KEY"))


CANDIDATE_PATH = "candidate.lean"
REFERENCE_PATH = "Tutorial/Lean/moduleOneRevised.lean"
with open(REFERENCE_PATH, "r", encoding="utf-8") as reference_spec:
            REFERENCE_SPEC = reference_spec.read()
IMPORT_LINE = "import Tutorial.Lean.moduleOneRevised"
SYSTEM_PROMPT = f"""
You are a Lean theorem prover.

The following Lean specification is immutable.
You may only use definitions from this specification.
Any symptom that is identified or ruled out should be supported by the user prompt. 

{REFERENCE_SPEC}

RULES:
- Do not modify imports.
- Do not change theorem statements.
"""


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
                "text": SYSTEM_PROMPT,
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
    # temp statement to see if caching is active 
    print(message.usage) 
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


# Helper function that implements a loop to repair errors and get a safe plan. 
# Also ensures that the plan is not trivially true or too simple 
def repair_loop(max_attempts=5):
    for attempt in range(max_attempts):
        print(f"\n[Repair Attempt {attempt+1}]")
        prompt = ""
        # Run the Lean code to capture the diagnostics and return values 
        returncode, stdout, stderr = run_lean(CANDIDATE_PATH)
        print(stdout)

        with open(CANDIDATE_PATH, "r", encoding="utf-8") as f:
            candidate_code = f.read()
        # Check to make sure the plan is sound and not too simple
        if not sound_proof(candidate_code) : 
            prompt += "The proof was rejected because it contains an incomplete proof placeholder.\n"
        elif returncode == 0 : 
            print("SAFE and SOUND: No violating instance exists.")
            return True

        prompt += f"""
You are repairing a Lean plan.

The theorem that the candidate plan is safe is not proven correctly. 

GOAL:
Modify the candidate plan so that the proof of its safety is provable. Then prove it. 

RULES:
- Only use variables, signatures, and fields already defined in the file below. Do NOT invent new names.
- Do not use trivially correct proofs (e.g. 'sorry') 

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
def generate_plan(user_prompt):
    with open(CANDIDATE_PATH, "r", encoding="utf-8") as f:
            candidate_code = f.read()

    prompt = f"""
You have been given a medical scenario: {user_prompt}

GOAL: 
produce the correct answer in Lean and prove its correctness. 

The Lean specification has already been provided in the system prompt (will NOT be modified)

RULES: 
- Use ONLY variables, signatures, and fields already defined in the file below
- Do NOT invent new names

WHAT YOU WILL BE MODIFYING (you will define the plan and prove it): 
{candidate_code} 
"""

    return call_claude(prompt, temperature=0.7)


# The full pipeline of generating the initial plan, repairing syntax errors , then repairing logic errors if the generated plan is not safe
def generate_and_verify(user_prompt, rounds=1):
    for i in range(rounds):
        print(f"\n == Pipleline round {i+1} ==")

        # generate plan
        generated_response = generate_plan(user_prompt)
        save_file(generated_response, CANDIDATE_PATH) 

        # logic phase
        if repair_loop():
            print("SAFE PLAN VERIFIED")
            with open(CANDIDATE_PATH, "r", encoding="utf-8") as f:
                candidate_code = f.read()
            print(natural_language(user_prompt, candidate_code))
            return True

    print("Failed to produce safe plan")
    return False

def natural_language(user_prompt, candidate_code):
    prompt = f"""
Translate the verified response from Lean to natural language. Be sure to address the initial question of the user. 
If more information was needed for diagnosis, ask an appropriate question that will guide the decision making process.
Use only information supported by the reference procedure and the verified Lean plan.

user prompt: 
{user_prompt}

Reference medical procedure
The Lean specification has already been provided in the system prompt.

verified LLM plan:
{candidate_code}

 """
    return call_claude(prompt, temperature=0.7)
# ------------------ Main ------------------
def main():

    prompt = input("Enter your medical scenario to be triaged:\n> ")
    generate_and_verify(prompt)



if __name__ == "__main__":
    main()