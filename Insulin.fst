module Insulin

(* Blood sugar level thresholds  *)
let normal_high = 130
let max_reading = 600

(* Fixed insulin dose  when sugar is high *)
let standard_dose = 10

(* Refinement type: ensures blood sugar reading is realistic and positive *)
type blood_sugar = s:int{s > 0 && s < max_reading}

(* Refinement type: ensures insulin dose is safe *)
type insulin_dose = d:int{d >= 0 && d <= 20}

(*
  LEMMA 1: Standard Dose is Safe
  Proves that our fixed standard_dose is within safe limits 
*)
val lemma_standard_dose_safe: unit ->
  Lemma (ensures (standard_dose >= 0 /\ standard_dose <= 20))
let lemma_standard_dose_safe () =
  // This is obvious since standard_dose = 10, but we prove it formally
  () 
  
val decide_insulin: sugar:blood_sugar -> 
  result:(option insulin_dose){
    // Safety: no insulin when sugar is at or below threshold
    (sugar <= normal_high ==> result = None) /\
    // When sugar is high, we give the standard dose
    (sugar > normal_high ==> result = Some standard_dose)
  }
let decide_insulin sugar =
  lemma_standard_dose_safe ();
  if sugar > normal_high then
    Some standard_dose  // Give 10 units of insulin
  else
    None  // Blood sugar is safe, no insulin needed
  
(*
  LEMMA 2: Safety - No Dose When Sugar Is Normal or Low
  This prevents dangerous hypoglycemia
*)
val lemma_no_insulin_when_safe: sugar:blood_sugar{sugar <= normal_high} ->
  Lemma (ensures (decide_insulin sugar = None))
let lemma_no_insulin_when_safe sugar =
  // The proof is straightforward from the function definition
  ()

let test_normal_sugar () : unit =
  lemma_no_insulin_when_safe 100;
  assert(decide_insulin 100 = None)

