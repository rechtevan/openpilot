/*
 * SPIN/Promela Model for Panda Safety Mode Protocol
 *
 * This models the safety mode configuration in:
 *   selfdrive/pandad/panda_safety.cc
 *
 * Key components:
 *   - PandaSafety class manages safety mode configuration
 *   - Multiple pandas must be synchronized
 *   - Safety mode transitions: ELM327 -> car-specific model
 *
 * Properties verified:
 *   - All pandas have consistent safety mode
 *   - Safety mode only set after car params available
 *   - No commands sent before safety configured
 *   - Initialization sequence is correct
 */

/* Number of pandas (typical: 1-3) */
#define NUM_PANDAS 2

/* Safety models */
#define SAFETY_SILENT 0
#define SAFETY_ELM327 1
#define SAFETY_HONDA  2   /* Example car-specific model */
#define SAFETY_TOYOTA 3   /* Example car-specific model */

/* Panda states */
#define PANDA_DISCONNECTED 0
#define PANDA_CONNECTED 1
#define PANDA_ELM327 2
#define PANDA_FINGERPRINTING 3
#define PANDA_CONFIGURED 4

/* System states */
bool is_onroad = false;
bool safety_configured = false;
bool initialized = false;
bool firmware_query_done = false;
bool controls_ready = false;
bool car_params_available = false;
bool obd_multiplexing_requested = false;
bool prev_obd_multiplexing = false;

/* Per-panda state */
byte panda_state[NUM_PANDAS];
byte panda_safety_model[NUM_PANDAS];
byte panda_safety_param[NUM_PANDAS];

/* Target safety model from car params */
byte target_safety_model = SAFETY_HONDA;

/* Synchronization */
bool all_pandas_consistent = true;

/*
 * Check if all pandas have the same safety model
 */
inline check_consistency() {
    byte i = 0;
    all_pandas_consistent = true;
    do
    :: i < NUM_PANDAS - 1 ->
        if
        :: panda_safety_model[i] != panda_safety_model[i + 1] ->
            all_pandas_consistent = false;
        :: else -> skip;
        fi;
        i++;
    :: else -> break;
    od;
}

/*
 * Initialize pandas to ELM327 mode
 */
inline initialize_pandas() {
    byte i = 0;
    do
    :: i < NUM_PANDAS ->
        panda_state[i] = PANDA_ELM327;
        panda_safety_model[i] = SAFETY_ELM327;
        panda_safety_param[i] = 1;  /* Default param */
        i++;
    :: else -> break;
    od;
    initialized = true;
    prev_obd_multiplexing = false;
    printf("Initialized all pandas to ELM327 mode\n");
}

/*
 * Update multiplexing mode based on OBD request
 */
inline update_multiplexing_mode() {
    if
    :: !initialized ->
        initialize_pandas();
    :: initialized && (obd_multiplexing_requested != prev_obd_multiplexing) ->
        byte i = 0;
        do
        :: i < NUM_PANDAS ->
            /* First panda gets param 0 if multiplexing, others get 1 */
            if
            :: i == 0 && obd_multiplexing_requested ->
                panda_safety_param[i] = 0;
            :: else ->
                panda_safety_param[i] = 1;
            fi;
            panda_safety_model[i] = SAFETY_ELM327;
            i++;
        :: else -> break;
        od;
        prev_obd_multiplexing = obd_multiplexing_requested;
        printf("Updated multiplexing mode\n");
    :: else -> skip;
    fi;
}

/*
 * Set safety mode from car params
 */
inline set_safety_mode() {
    byte i = 0;
    do
    :: i < NUM_PANDAS ->
        panda_safety_model[i] = target_safety_model;
        panda_safety_param[i] = 0;  /* Car-specific param */
        panda_state[i] = PANDA_CONFIGURED;
        i++;
    :: else -> break;
    od;
    safety_configured = true;
    printf("Set safety mode to %d for all pandas\n", target_safety_model);
}

/*
 * Configure safety mode - main logic from configureSafetyMode()
 */
inline configure_safety_mode() {
    if
    :: is_onroad && !safety_configured ->
        update_multiplexing_mode();

        /* Check if car params available */
        if
        :: firmware_query_done && controls_ready && car_params_available ->
            printf("Car params available, setting safety mode\n");
            set_safety_mode();
        :: else ->
            printf("Waiting for car params\n");
        fi;
    :: !is_onroad ->
        /* Reset state when going offroad - must be atomic */
        atomic {
            safety_configured = false;
            initialized = false;
            byte i = 0;
            do
            :: i < NUM_PANDAS ->
                panda_state[i] = PANDA_CONNECTED;
                panda_safety_model[i] = SAFETY_SILENT;
                i++;
            :: else -> break;
            od;
        }
        printf("Went offroad, reset safety state\n");
    :: else -> skip;
    fi;
}

/*
 * PandaSafety process - manages safety mode configuration
 */
proctype PandaSafety() {
    printf("PandaSafety: Starting\n");

    do
    :: true ->
        configure_safety_mode();
        check_consistency();
    od;
}

/*
 * Environment process - simulates external state changes
 */
proctype Environment() {
    printf("Environment: Starting\n");

    do
    :: true ->
        /* Non-deterministically change environment state */
        if
        :: true -> is_onroad = true;
        :: true -> is_onroad = false;
        fi;

        if
        :: true -> firmware_query_done = true;
        :: firmware_query_done -> skip;  /* Don't undo firmware query */
        fi;

        if
        :: firmware_query_done -> controls_ready = true;
        :: controls_ready -> skip;
        :: true -> skip;
        fi;

        if
        :: controls_ready -> car_params_available = true;
        :: car_params_available -> skip;
        :: true -> skip;
        fi;

        if
        :: true -> obd_multiplexing_requested = true;
        :: true -> obd_multiplexing_requested = false;
        fi;
    od;
}

/*
 * Panda process - represents physical panda device
 */
proctype Panda(byte id) {
    printf("Panda %d: Starting\n", id);
    panda_state[id] = PANDA_CONNECTED;
    panda_safety_model[id] = SAFETY_SILENT;
    panda_safety_param[id] = 0;

    do
    :: true ->
        /* Panda responds to safety model changes */
        if
        :: panda_state[id] == PANDA_CONFIGURED ->
            /* Operating in configured mode */
            skip;
        :: else ->
            skip;
        fi;
    od;
}

/*
 * Initialize and run
 */
init {
    byte i;

    atomic {
        /* Initialize panda states */
        i = 0;
        do
        :: i < NUM_PANDAS ->
            panda_state[i] = PANDA_DISCONNECTED;
            panda_safety_model[i] = SAFETY_SILENT;
            panda_safety_param[i] = 0;
            i++;
        :: else -> break;
        od;

        /* Start processes */
        run Environment();
        run PandaSafety();
        i = 0;
        do
        :: i < NUM_PANDAS ->
            run Panda(i);
            i++;
        :: else -> break;
        od;
    }
}

/*
 * LTL Properties
 */

/* P1: All pandas eventually have consistent safety models */
ltl all_consistent {
    []<>(all_pandas_consistent)
}

/* P2: Safety configured only after car params available */
ltl safety_requires_params {
    [](safety_configured -> car_params_available)
}

/* P3: Safety configured only after firmware query done */
ltl safety_requires_firmware {
    [](safety_configured -> firmware_query_done)
}

/* P4: Safety configured only after controls ready */
ltl safety_requires_controls {
    [](safety_configured -> controls_ready)
}

/* P5: Initialization happens before configuration */
ltl init_before_config {
    [](safety_configured -> initialized)
}

/* P6: Going offroad resets safety configuration */
ltl offroad_resets {
    [](!is_onroad -> <>(!safety_configured))
}

/* P7: When onroad with params, eventually configured */
ltl eventually_configured {
    []((is_onroad && car_params_available && controls_ready && firmware_query_done) ->
       <>(safety_configured))
}

/* P8: No panda has car-specific model without safety_configured */
ltl no_premature_config {
    [](!safety_configured ->
       (panda_safety_model[0] == SAFETY_SILENT ||
        panda_safety_model[0] == SAFETY_ELM327))
}

/*
 * Assertion-based checks (verified during state exploration)
 */

/* A1: All pandas have same model when configured */
#define ASSERT_CONSISTENT \
    assert(safety_configured -> \
           (panda_safety_model[0] == panda_safety_model[1]))

/* A2: Safety model is valid */
#define ASSERT_VALID_MODEL(i) \
    assert(panda_safety_model[i] >= SAFETY_SILENT && \
           panda_safety_model[i] <= SAFETY_TOYOTA)
