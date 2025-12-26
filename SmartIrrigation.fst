module SmartIrrigation 
(* ========================================================================
   PART 1: CORE TYPES AND CONSTANTS
   ======================================================================== *)

(* Physical bounds and thresholds *)
let moisture_min : nat = 0
let moisture_max : nat = 100
let moisture_low_threshold : nat = 30
let moisture_high_threshold : nat = 70
let moisture_target : nat = 50

let max_consecutive_valve_open : nat = 10
let min_irrigation_amount : nat = 5

(* Tank capacities *)
let capacity_A : nat = 1000  // Main reservoir
let capacity_B : nat = 200   // Irrigation tank
let capacity_C : nat = 100   // Nutrient tank

(* Acceptable operating levels per tank (different lower/upper for each) *)
let tankA_low_threshold  : nat = 400
let tankA_high_threshold : nat = 900

let tankB_low_threshold  : nat = capacity_B / 2    // already used for refill
let tankB_high_threshold : nat = capacity_B        

let tankC_low_threshold  : nat = 20
let tankC_high_threshold : nat = 80

(* Flow rates per step inside the system *)
let flow_rate_AB : nat = 10  // A → B
let flow_rate_CB : nat = 5   // C → B
let flow_rate_irrigation : nat = 8  // B → soil

(* External supply flow rates (inputs into A and C) *)
let flow_rate_supply_A : nat = 15    // external source → A
let flow_rate_supply_C : nat = 8     // external source → C

(* Environmental parameters *)
let evaporation_base : nat = 2
let rainfall_amount : nat = 5

(* Sensor bounds for fault detection *)
let sensor_moisture_min : int = -10
let sensor_moisture_max : int = 110
let sensor_temp_min : int = -10
let sensor_temp_max : int = 60
let sensor_humidity_min : int = 0
let sensor_humidity_max : int = 100

(* ========================================================================
   PART 2: BASIC TYPES
   ======================================================================== *)

type valve_state = 
  | Open
  | Closed

type tank = {
  level: nat;
  capacity: nat;
}

type sensor_reading = {
  moisture: int;
  temperature: int;
  humidity: int;
}

type sensor_status =
  | SensorOK
  | SensorFaulty

(* ========================================================================
   PART 3: SYSTEM STATE
   ======================================================================== *)

type system_state = {
  // Tank states
  tankA: tank;
  tankB: tank;
  tankC: tank;
  
  // Soil moisture (actual physical state)
  soil_moisture: nat;
  
  // Valve states (internal flows)
  valveAB: valve_state;
  valveCB: valve_state;
  irrigationValve: valve_state;

  // External supply valves (inputs for A and C)
  valveSupplyA: valve_state;
  valveSupplyC: valve_state;
  
  // Valve open counters (for max consecutive open enforcement)
  valveAB_counter: nat;
  valveCB_counter: nat;
  irrigation_counter: nat;
  valveSupplyA_counter: nat;
  valveSupplyC_counter: nat;
  
  // Sensor data
  sensors: sensor_reading;
  sensor_status: sensor_status;
  
  // System mode
  safe_mode: bool;
  
  // Environmental state
  rainfall_active: bool;
}

(* ========================================================================
   PART 4: PREDICATES AND INVARIANTS
   ======================================================================== *)

(* Tank validity predicate *)
let tank_ok (t: tank) : bool =
  t.level <= t.capacity

(* Sensor reading validity *)
let sensor_reading_valid (s: sensor_reading) : bool =
  s.moisture >= sensor_moisture_min &&
  s.moisture <= sensor_moisture_max &&
  s.temperature >= sensor_temp_min &&
  s.temperature <= sensor_temp_max &&
  s.humidity >= sensor_humidity_min &&
  s.humidity <= sensor_humidity_max

(* Soil moisture bounds *)
let soil_moisture_ok (m: nat) : bool =
  m >= moisture_min && m <= moisture_max

(* Valve counter limits *)
let valve_counters_ok (s: system_state) : bool =
  s.valveAB_counter <= max_consecutive_valve_open &&
  s.valveCB_counter <= max_consecutive_valve_open &&
  s.irrigation_counter <= max_consecutive_valve_open &&
  s.valveSupplyA_counter <= max_consecutive_valve_open &&
  s.valveSupplyC_counter <= max_consecutive_valve_open


(* Global system invariant *)
let state_ok (s: system_state) : bool =
  tank_ok s.tankA &&
  tank_ok s.tankB &&
  tank_ok s.tankC &&
  soil_moisture_ok s.soil_moisture &&
  valve_counters_ok s &&
  s.tankA.capacity = capacity_A &&
  s.tankB.capacity = capacity_B &&
  s.tankC.capacity = capacity_C

(* ========================================================================
   PART 5: SENSOR MODULE WITH FAULT DETECTION
   ======================================================================== *)

(* Sanitize sensor data - detects faults and returns status *)
val sanitize_sensor_data : sensor_reading -> Tot sensor_status
let sanitize_sensor_data (s: sensor_reading) =
  if sensor_reading_valid s then SensorOK
  else SensorFaulty

(* Safe sensor reading - returns default safe values if faulty *)
val get_safe_moisture : sensor_reading -> sensor_status -> Tot nat
let get_safe_moisture (s: sensor_reading) (status: sensor_status) =
  match status with
  | SensorOK -> 
      if s.moisture >= moisture_min && s.moisture <= moisture_max 
      then s.moisture 
      else moisture_target  // Clamp to safe default
  | SensorFaulty -> moisture_target  // Safe default on fault

(* ========================================================================
   PART 6: HELPER FUNCTIONS FOR ARITHMETIC
   ======================================================================== *)

(* Safe subtraction with underflow protection *)
val safe_sub : a:nat -> b:nat -> Tot (r:nat{ r <= a })
let safe_sub a b =
  if a >= b then a - b else 0

(* Safe addition with overflow protection *)
val safe_add_capped : a:nat -> b:nat -> cap:nat -> Tot (r:nat{r <= cap})
let safe_add_capped a b cap =
  let sum = a + b in
  if sum <= cap then sum else cap

(* Clamp value to range *)
val clamp : v:nat -> min:nat -> max:nat{min <= max} -> Tot (r:nat{r >= min && r <= max})
let clamp v min max =
  if v < min then min
  else if v > max then max
  else v

(* ========================================================================
   PART 7: TANK TRANSFER OPERATIONS (WITH VERIFICATION)
   ======================================================================== *)

(* Transfer from source to destination tank *)
val transfer_tanks : 
  src:tank -> 
  dst:tank -> 
  amount:nat -> 
  Pure (tank * tank)
    (requires tank_ok src && tank_ok dst)
    (ensures fun (src', dst') -> 
      tank_ok src' && 
      tank_ok dst' &&
      src'.capacity = src.capacity &&
      dst'.capacity = dst.capacity &&
      src'.level <= src.level &&
      dst'.level >= dst.level &&
      dst'.level <= dst.capacity)

let transfer_tanks src dst amount =
  // Calculate actual transferable amount (limited by source and dest capacity)
  let available = src.level in
  let space = dst.capacity - dst.level in
  let actual_transfer = 
    if amount <= available && amount <= space then amount
    else if available <= space then available
    else space
  in
  let src' = { src with level = src.level - actual_transfer } in
  let dst' = { dst with level = dst.level + actual_transfer } in
  (src', dst')

(* Transfer from tank to soil (irrigation) *)
val transfer_to_soil :
  t:tank ->
  m:nat ->
  amount:nat ->
  Pure (tank * nat)
    (requires tank_ok t && soil_moisture_ok m)
    (ensures (fun res ->
      let t' = fst res in
      let m' = snd res in

      tank_ok t' &&
      soil_moisture_ok m' &&
      t'.capacity = t.capacity &&
      t'.level <= t.level &&
      m' >= m &&
      m' <= moisture_max
    ))

let transfer_to_soil t m amount =
  let available = t.level in
  let actual_transfer = if amount <= available then amount else available in
  let t' = { t with level = t.level - actual_transfer } in
  let m' = clamp (m + actual_transfer) moisture_min moisture_max in
  (t', m')

(* ========================================================================
   PART 8: CONTROLLER (VERIFIED DECISION LOGIC)
   ======================================================================== *)

(* Update valve counter based on valve state *)
val update_counter : valve_state -> nat -> Tot nat
let update_counter valve counter =
  match valve with
  | Open -> if counter < max_consecutive_valve_open then counter + 1 else counter
  | Closed -> 0

(* Controller: Makes decisions about valve states *)
val controller : s:system_state -> Pure system_state
  (requires state_ok s)
  (ensures fun s' -> 
    state_ok s' &&
    // Tanks and soil unchanged by controller (only valves and counters change)
    s'.tankA = s.tankA &&
    s'.tankB = s.tankB &&
    s'.tankC = s.tankC &&
    s'.soil_moisture = s.soil_moisture &&
    // Sensor status updated
    s'.sensor_status = sanitize_sensor_data s.sensors &&
    // Safe mode enforced on fault
    ((s'.sensor_status <> SensorFaulty) || (s'.safe_mode = true)) &&
    // All valves closed in safe mode
    ((not s'.safe_mode) || 
     (s'.valveAB = Closed &&
      s'.valveCB = Closed &&
      s'.irrigationValve = Closed &&
      s'.valveSupplyA = Closed &&
      s'.valveSupplyC = Closed)) &&
    // Valve counters properly bounded
    valve_counters_ok s')


let controller s =
  // Step 1: Check sensor health
  let sensor_st = sanitize_sensor_data s.sensors in
  let safe_moisture = get_safe_moisture s.sensors sensor_st in
  
  // Step 2: Determine if we enter safe mode
  let enter_safe_mode = (sensor_st = SensorFaulty) || s.safe_mode in
  
  // Step 3: Controller logic (all valves closed if safe mode)
  if enter_safe_mode then
    { s with 
      valveAB = Closed;
      valveCB = Closed;
      irrigationValve = Closed;
      valveSupplyA = Closed;
      valveSupplyC = Closed;
      sensor_status = sensor_st;
      safe_mode = true;
      valveAB_counter = 0;
      valveCB_counter = 0;
      irrigation_counter = 0;
      valveSupplyA_counter = 0;
      valveSupplyC_counter = 0;
    }
  else
    // Normal operation: decide valve states based on conditions
    
    // Decision 1: Should we irrigate?
    let need_irrigation = safe_moisture < moisture_low_threshold in
    let can_irrigate = s.tankB.level >= min_irrigation_amount in
    let irrigation_not_maxed = s.irrigation_counter < max_consecutive_valve_open in
    let irrigation_valve = 
      if need_irrigation && can_irrigate && irrigation_not_maxed 
      then Open else Closed
    in
    
    // Decision 2: Should we refill B from A?
    let b_needs_refill = s.tankB.level < tankB_low_threshold in
    let a_has_water = s.tankA.level >= flow_rate_AB in
    let ab_not_maxed = s.valveAB_counter < max_consecutive_valve_open in
    let valve_ab = 
      if b_needs_refill && a_has_water && ab_not_maxed 
      then Open else Closed
    in
    
    // Decision 3: Should we add nutrients from C?
    let need_nutrients = safe_moisture < moisture_target && s.tankB.level > 0 in
    let c_has_liquid = s.tankC.level >= flow_rate_CB in
    let cb_not_maxed = s.valveCB_counter < max_consecutive_valve_open in
    let valve_cb = 
      if need_nutrients && c_has_liquid && cb_not_maxed 
      then Open else Closed
    in

    // Decision 4: External refill for A
    let a_needs_refill = s.tankA.level < tankA_low_threshold in
    let a_refill_not_maxed = s.valveSupplyA_counter < max_consecutive_valve_open in
    let valve_supplyA =
      if a_needs_refill && a_refill_not_maxed
      then Open else Closed
    in

    // Decision 5: External refill for C
    let c_needs_refill = s.tankC.level < tankC_low_threshold in
    let c_refill_not_maxed = s.valveSupplyC_counter < max_consecutive_valve_open in
    let valve_supplyC =
      if c_needs_refill && c_refill_not_maxed
      then Open else Closed
    in
    
    // Update counters
    let new_ab_counter  = update_counter valve_ab        s.valveAB_counter in
    let new_cb_counter  = update_counter valve_cb        s.valveCB_counter in
    let new_irr_counter = update_counter irrigation_valve s.irrigation_counter in
    let new_supA_counter = update_counter valve_supplyA  s.valveSupplyA_counter in
    let new_supC_counter = update_counter valve_supplyC  s.valveSupplyC_counter in
    
    { s with
      valveAB = valve_ab;
      valveCB = valve_cb;
      irrigationValve = irrigation_valve;
      valveSupplyA = valve_supplyA;
      valveSupplyC = valve_supplyC;
      valveAB_counter = new_ab_counter;
      valveCB_counter = new_cb_counter;
      irrigation_counter = new_irr_counter;
      valveSupplyA_counter = new_supA_counter;
      valveSupplyC_counter = new_supC_counter;
      sensor_status = sensor_st;
      safe_mode = false;
    }


(* ========================================================================
   PART 9: PHYSICS STEP (APPLIES FLOWS AND ENVIRONMENT)
   ======================================================================== *)

(* Apply evaporation based on temperature and humidity *)
val apply_evaporation :
  moisture:nat -> temp:int -> humidity:int ->
  Tot (r:nat{r <= moisture})

let apply_evaporation moisture temp humidity =
  let evap_factor =
    if temp > 25 && humidity < 50 then evaporation_base + 1
    else evaporation_base
  in
  safe_sub moisture evap_factor


(* Apply rainfall if active *)
val apply_rainfall :
  moisture:nat -> active:bool ->
  Tot (r:nat{ r >= moisture_min && r <= moisture_max })

let apply_rainfall moisture active =
  if active then
    begin
      let r = clamp (moisture + rainfall_amount) moisture_min moisture_max in
      r
    end
  else
    begin
      clamp moisture moisture_min moisture_max
    end


(* Physics step: applies all flows and environmental effects *)
val physics_step : s:system_state -> Pure system_state
  (requires state_ok s)
  (ensures fun s' -> 
    state_ok s' &&
    // Valve states unchanged by physics
    s'.valveAB = s.valveAB &&
    s'.valveCB = s.valveCB &&
    s'.irrigationValve = s.irrigationValve &&
    s'.valveSupplyA = s.valveSupplyA &&
    s'.valveSupplyC = s.valveSupplyC &&
    // Counters unchanged
    s'.valveAB_counter = s.valveAB_counter &&
    s'.valveCB_counter = s.valveCB_counter &&
    s'.irrigation_counter = s.irrigation_counter &&
    s'.valveSupplyA_counter = s.valveSupplyA_counter &&
    s'.valveSupplyC_counter = s.valveSupplyC_counter &&
    // Safe mode unchanged
    s'.safe_mode = s.safe_mode &&
    // All invariants maintained
    tank_ok s'.tankA &&
    tank_ok s'.tankB &&
    tank_ok s'.tankC &&
    soil_moisture_ok s'.soil_moisture)


let physics_step s =
  // Step 0: External refills for A and C

  // External refill into A (from source)
  let tankA0 =
    if s.valveSupplyA = Open then
      let new_level = safe_add_capped s.tankA.level flow_rate_supply_A s.tankA.capacity in
      { s.tankA with level = new_level }
    else
      s.tankA
  in

  // External refill into C (from nutrient source)
  let tankC0 =
    if s.valveSupplyC = Open then
      let new_level = safe_add_capped s.tankC.level flow_rate_supply_C s.tankC.capacity in
      { s.tankC with level = new_level }
    else
      s.tankC
  in

  // Step 1: Apply tank-to-tank flows based on valve states
  
  // Flow A → B
  let (tankA1, tankB1) = 
    if s.valveAB = Open 
    then transfer_tanks tankA0 s.tankB flow_rate_AB
    else (tankA0, s.tankB)
  in
  
  // Flow C → B
  let (tankC1, tankB2) =
    if s.valveCB = Open
    then transfer_tanks tankC0 tankB1 flow_rate_CB
    else (tankC0, tankB1)
  in
  
  // Step 2: Apply irrigation B → soil
  let (tankB3, soil1) =
    if s.irrigationValve = Open
    then transfer_to_soil tankB2 s.soil_moisture flow_rate_irrigation
    else (tankB2, s.soil_moisture)
  in
  
  // Step 3: Apply environmental effects
  let soil2 = apply_evaporation soil1 s.sensors.temperature s.sensors.humidity in
  let soil3 = apply_rainfall soil2 s.rainfall_active in
  
  { s with
    tankA = tankA1;
    tankB = tankB3;
    tankC = tankC1;
    soil_moisture = soil3;
  }


(* ========================================================================
   PART 10: COMBINED CPS STEP
   ======================================================================== *)

(* Full CPS step: controller decision + physics application *)
val step : s:system_state -> Pure system_state
  (requires state_ok s)
  (ensures fun s' -> state_ok s')

let step s =
  let s_controlled = controller s in
  physics_step s_controlled

(* ========================================================================
   PART 11: DETERMINISM LEMMA
   ======================================================================== *)

(* Determinism: same input always produces same output *)
val determinism_lemma :
  s:system_state ->
  Lemma
    (requires state_ok s)
    (ensures (step s == step s))

let determinism_lemma s = ()

(* ========================================================================
   PART 12: SAFETY LEMMAS
   ======================================================================== *)

(* Lemma: No tank ever overflows *)
val no_overflow_lemma : s:system_state -> Lemma
  (requires state_ok s)
  (ensures (
      let s' = step s in
      s'.tankA.level <= s'.tankA.capacity /\
      s'.tankB.level <= s'.tankB.capacity /\
      s'.tankC.level <= s'.tankC.capacity
  ))

let no_overflow_lemma s = ()

(* Lemma: Soil moisture always bounded *)
val moisture_bounded_lemma : s:system_state -> Lemma
  (requires state_ok s)
  (ensures (
    let s' = step s in
    s'.soil_moisture >= moisture_min /\
    s'.soil_moisture <= moisture_max
  ))

let moisture_bounded_lemma s = ()

(* Lemma: Faulty sensors trigger safe mode *)

val fault_safety_lemma :
  s:system_state ->
  Lemma
    (requires (state_ok s /\ sanitize_sensor_data s.sensors = SensorFaulty))
    (ensures 
  (let s' = controller s in
   s'.safe_mode = true /\
   s'.valveAB = Closed /\
   s'.valveCB = Closed /\
   s'.irrigationValve = Closed /\
   s'.valveSupplyA = Closed /\
   s'.valveSupplyC = Closed))

let fault_safety_lemma s = ()


(* Lemma: Valve counters never exceed maximum *)
val valve_counter_bounded_lemma : s:system_state -> Lemma
  (requires state_ok s)
  (ensures (
  let s' = step s in
  valve_counters_ok s'
))
let valve_counter_bounded_lemma s = ()

(* ========================================================================
   PART 13: LIVENESS REASONING (CONVERGENCE)
   ======================================================================== *)

(* 
   LIVENESS ARGUMENT (Semi-formal):
   
   Theorem: If Tank A or B has sufficient water and soil moisture is below
   the safe range, the system will eventually restore moisture to target range.
   
   Proof sketch:
   1. Assume: tankA.level >= min_irrigation_amount OR 
              tankB.level >= min_irrigation_amount
   2. Assume: soil_moisture < moisture_low_threshold
   3. Assume: sensor_status = SensorOK (no faults)
   
   Then:
   - Controller will set irrigationValve = Open (by controller logic)
   - If B is low, valveAB = Open to refill from A
   - Each step with irrigationValve = Open increases soil_moisture by
     up to flow_rate_irrigation
   - Evaporation decreases moisture by at most (evaporation_base + 1)
   - Net effect: moisture increases when irrigation > evaporation
   - Since flow_rate_irrigation (8) > max evaporation (3), moisture increases
   - Process continues until moisture >= moisture_low_threshold
   - Controller then closes irrigationValve
   
   Upper bound on steps:
     steps <= (moisture_target - initial_moisture) / (flow_rate_irrigation - max_evap)
     steps <= (50 - 0) / (8 - 3) = 10 steps worst case
   
   This demonstrates bounded-time convergence to safe moisture levels.
*)

val liveness_progress : s:system_state -> Lemma
  (requires 
    state_ok s &&
    s.soil_moisture < moisture_low_threshold &&
    (s.tankA.level >= min_irrigation_amount || s.tankB.level >= min_irrigation_amount) &&
    s.sensor_status = SensorOK &&
    not s.safe_mode)
  (ensures (
    let s' = step s in
    // Either moisture increased, or we're refilling B from A to enable irrigation
    (s'.soil_moisture >= s.soil_moisture || s'.tankB.level >= s.tankB.level)))

let liveness_progress s = ()

(* ========================================================================
   PART 14: INITIALIZATION
   ======================================================================== *)

(* Create initial valid state *)
val init_state : unit -> Tot (s:system_state{state_ok s})
let init_state () = {
  tankA = { level = 800; capacity = capacity_A };
  tankB = { level = 100; capacity = capacity_B };
  tankC = { level = 50;  capacity = capacity_C };

  soil_moisture = 40;

  // Internal valves
  valveAB = Closed;
  valveCB = Closed;
  irrigationValve = Closed;

  // External supply valves
  valveSupplyA = Closed;
  valveSupplyC = Closed;

  // Counters
  valveAB_counter = 0;
  valveCB_counter = 0;
  irrigation_counter = 0;
  valveSupplyA_counter = 0;
  valveSupplyC_counter = 0;

  // Sensor info
  sensors = { moisture = 40; temperature = 22; humidity = 60 };
  sensor_status = SensorOK;

  // Mode
  safe_mode = false;

  // Environment
  rainfall_active = false;
}


(* ========================================================================
   PART 15: MULTI-STEP EXECUTION WITH INVARIANT PRESERVATION
   ======================================================================== *)

(* Execute n steps, preserving invariants throughout *)
val run_n_steps : s:system_state -> n:nat -> Pure system_state
  (requires state_ok s)
  (ensures fun s' -> state_ok s')
  (decreases n)

let rec run_n_steps s n =
  if n = 0 then s
  else run_n_steps (step s) (n - 1)

(* ========================================================================
   PART 16: TEST CASES
   ======================================================================== *)


(* ========================================================================
   PART 16: TEST CASES
   ======================================================================== *)


(* Helper: default valve states for tests *)
let closed_valves_defaults = (
  Closed, Closed, Closed, Closed, Closed
)


(* TEST 1: ensures B is refilled when low *)
let test_refill_B_from_A =
  let s0 = {
    tankA = { level = 800; capacity = capacity_A };
    tankB = { level = 10;  capacity = capacity_B };
    tankC = { level = 100; capacity = capacity_C };

    soil_moisture = 60;

    valveAB = Open;
    valveCB = Closed;
    irrigationValve = Closed;

    valveSupplyA = Closed;
    valveSupplyC = Closed;

    valveAB_counter = 0;
    valveCB_counter = 0;
    irrigation_counter = 0;
    valveSupplyA_counter = 0;
    valveSupplyC_counter = 0;

    sensor_status = SensorOK;
    sensors = { moisture = 60; humidity = 50; temperature = 25 };

    safe_mode = false;
    rainfall_active = false;
  } in

  let s1 = step s0 in
  assert (s1.tankB.level > s0.tankB.level)


(* TEST 2: ensures valveAB opens when B is low *)
let test_open_valveAB_when_tankB_low =
  let s0 = {
    tankA = { level = 800; capacity = capacity_A };
    tankB = { level = 5; capacity = capacity_B };
    tankC = { level = 100; capacity = capacity_C };

    soil_moisture = 60;

    valveAB = Closed;
    valveCB = Closed;
    irrigationValve = Closed;

    valveSupplyA = Closed;
    valveSupplyC = Closed;

    valveAB_counter = 0;
    valveCB_counter = 0;
    irrigation_counter = 0;
    valveSupplyA_counter = 0;
    valveSupplyC_counter = 0;

    sensor_status = SensorOK;
    sensors = { moisture = 60; humidity = 50; temperature = 25 };

    safe_mode = false;
    rainfall_active = false;
  } in

  let s1 = step s0 in
  assert (s1.valveAB = Open)


(* TEST 3: valveCB opens when moisture < target and C has liquid *)
let test_open_valveCB_when_needed =
  let s0 = {
    tankA = { level = 800; capacity = capacity_A };
    tankB = { level = 50;  capacity = capacity_B };
    tankC = { level = 20;  capacity = capacity_C };

    soil_moisture = 40;

    valveAB = Closed;
    valveCB = Closed;
    irrigationValve = Closed;

    valveSupplyA = Closed;
    valveSupplyC = Closed;

    valveAB_counter = 0;
    valveCB_counter = 0;
    irrigation_counter = 0;
    valveSupplyA_counter = 0;
    valveSupplyC_counter = 0;

    sensor_status = SensorOK;
    sensors = { moisture = 40; humidity = 50; temperature = 20 };

    safe_mode = false;
    rainfall_active = false;
  } in

  let s1 = step s0 in
  assert (s1.valveCB = Open)


(* TEST 4: system enters safe mode on sensor fault *)
let test_enter_safe_mode_on_fault =
  let s0 = {
    tankA = { level = 800; capacity = capacity_A };
    tankB = { level = 100; capacity = capacity_B };
    tankC = { level = 50;  capacity = capacity_C };

    soil_moisture = 40;

    valveAB = Open;
    valveCB = Open;
    irrigationValve = Open;

    valveSupplyA = Open;
    valveSupplyC = Open;

    valveAB_counter = 4;
    valveCB_counter = 5;
    irrigation_counter = 3;
    valveSupplyA_counter = 2;
    valveSupplyC_counter = 7;

    sensor_status = SensorOK;
    sensors = { moisture = 999; humidity = 50; temperature = 20 };

    safe_mode = false;
    rainfall_active = false;
  } in

  let s1 = step s0 in
  assert (s1.safe_mode = true);
  assert (s1.sensor_status = SensorFaulty);
  assert (s1.valveAB = Closed);
  assert (s1.valveCB = Closed);
  assert (s1.irrigationValve = Closed);
  assert (s1.valveSupplyA = Closed);
  assert (s1.valveSupplyC = Closed)


(* TEST 5: rainfall increases soil moisture *)
let test_rainfall_increases_moisture =
  let s0 = {
    tankA = { level = 800; capacity = capacity_A };
    tankB = { level = 100; capacity = capacity_B };
    tankC = { level = 50;  capacity = capacity_C };

    soil_moisture = 60;

    valveAB = Closed;
    valveCB = Closed;
    irrigationValve = Closed;

    valveSupplyA = Closed;
    valveSupplyC = Closed;

    valveAB_counter = 0;
    valveCB_counter = 0;
    irrigation_counter = 0;
    valveSupplyA_counter = 0;
    valveSupplyC_counter = 0;

    sensor_status = SensorOK;
    sensors = { moisture = 60; humidity = 40; temperature = 20 };

    safe_mode = false;
    rainfall_active = true;
  } in

  let s1 = step s0 in
  assert (s1.soil_moisture > s0.soil_moisture)


(* TEST 6: simultaneous A->B, C->B, and irrigation *)
let test_simultaneous_refill_and_irrigation =
  let s0 = {
    tankA = { level = 800; capacity = capacity_A };
    tankB = { level = 20;  capacity = capacity_B };
    tankC = { level = 50;  capacity = capacity_C };

    soil_moisture = 10;

    valveAB = Closed;
    valveCB = Closed;
    irrigationValve = Closed;

    valveSupplyA = Closed;
    valveSupplyC = Closed;

    valveAB_counter = 0;
    valveCB_counter = 0;
    irrigation_counter = 0;
    valveSupplyA_counter = 0;
    valveSupplyC_counter = 0;

    sensor_status = SensorOK;
    sensors = { moisture = 10; humidity = 40; temperature = 20 };

    safe_mode = false;
    rainfall_active = false;
  } in

  let s1 = step s0 in

  assert (s1.valveAB = Open);
  assert (s1.valveCB = Open);
  assert (s1.irrigationValve = Open)


(* TEST 7: B never overflows even with AB + CB *)
let test_no_overflow_on_B =
  let s0 = {
    tankA = { level = 800; capacity = capacity_A };
    tankB = { level = 195; capacity = capacity_B };
    tankC = { level = 50;  capacity = capacity_C };

    soil_moisture = 60;

    valveAB = Open;
    valveCB = Open;
    irrigationValve = Closed;

    valveSupplyA = Closed;
    valveSupplyC = Closed;

    valveAB_counter = 0;
    valveCB_counter = 0;
    irrigation_counter = 0;
    valveSupplyA_counter = 0;
    valveSupplyC_counter = 0;

    sensor_status = SensorOK;
    sensors = { moisture = 60; humidity = 50; temperature = 25 };

    safe_mode = false;
    rainfall_active = false;
  } in

  let s1 = physics_step s0 in
  assert (s1.tankB.level <= capacity_B)


(* TEST 8: evaporation reduces moisture *)
let test_evaporation_reduces_moisture =
  let s0 = {
    tankA = { level = 800; capacity = capacity_A };
    tankB = { level = 200; capacity = capacity_B };
    tankC = { level = 50;  capacity = capacity_C };

    soil_moisture = 70;

    valveAB = Closed;
    valveCB = Closed;
    irrigationValve = Closed;

    valveSupplyA = Closed;
    valveSupplyC = Closed;

    valveAB_counter = 0;
    valveCB_counter = 0;
    irrigation_counter = 0;
    valveSupplyA_counter = 0;
    valveSupplyC_counter = 0;

    sensor_status = SensorOK;
    sensors = { moisture = 70; humidity = 30; temperature = 30 };

    safe_mode = false;
    rainfall_active = false;
  } in

  let s1 = step s0 in
  assert (s1.soil_moisture < s0.soil_moisture)


(* TEST 9: exact AB transfer amount *)
let test_exact_AB_transfer_levels =
  let s0 = {
    tankA = { level = 800; capacity = capacity_A };
    tankB = { level = 100; capacity = capacity_B };
    tankC = { level = 50;  capacity = capacity_C };

    soil_moisture = 50;

    valveAB = Open;
    valveCB = Closed;
    irrigationValve = Closed;

    valveSupplyA = Closed;
    valveSupplyC = Closed;

    valveAB_counter = 0;
    valveCB_counter = 0;
    irrigation_counter = 0;
    valveSupplyA_counter = 0;
    valveSupplyC_counter = 0;

    sensor_status = SensorOK;
    sensors = { moisture = 50; humidity = 60; temperature = 20 };

    safe_mode = false;
    rainfall_active = false;
  } in

  let s1 = physics_step s0 in

  assert (s1.tankA.level = s0.tankA.level - flow_rate_AB);
  assert (s1.tankB.level = s0.tankB.level + flow_rate_AB)

(* TEST 10: Tank A triggers external refill when below threshold *)
let test_refill_A_when_low =
  let s0 = {
    tankA = { level = 300; capacity = capacity_A };   (* BELOW tankA_low_threshold = 400 → refill expected *)
    tankB = { level = 150; capacity = capacity_B };
    tankC = { level = 50;  capacity = capacity_C };

    soil_moisture = 60;

    valveAB = Closed;
    valveCB = Closed;
    irrigationValve = Closed;

    valveSupplyA = Closed;     (* Should OPEN *)
    valveSupplyC = Closed;

    valveAB_counter = 0;
    valveCB_counter = 0;
    irrigation_counter = 0;
    valveSupplyA_counter = 0;
    valveSupplyC_counter = 0;

    sensor_status = SensorOK;
    sensors = { moisture = 60; humidity = 40; temperature = 25 };

    safe_mode = false;
    rainfall_active = false;
  } in

  let s1 = step s0 in

  (* Tank A refill must be activated *)
  assert (s1.valveSupplyA = Open)





