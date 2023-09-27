open OUnit2
open Enigma

(* some instance variables *)
let rotor_abcd = "ABCDEFGHIJKLMNOPQRSTUVWXYZ"
let rotor_bacd = "BACDEFGHIJKLMNOPQRSTUVWXYZ"
let rotor_I = "EKMFLGDQVZNTOWYHXUSPAIBRCJ"
let rotor_II = "AJDKSIRUXBLHWTMCQGZNPYFVOE"
let rotor_III = "BDFHJLCPRTXVZNYEIWGAKMUSQO"
let reflector_abcd = "ABCDEFGHIJKLMNOPQRSTUVWXYZ"
let reflector_B = "YRUHQSLDPXNGOKMIEBFZCWVJAT"
let reflector_C = "FVPJIAOYEDRZXWGCTKUQSBNMHL"
let rotor_I' : rotor = { wiring = rotor_I; turnover = 'B' }
let oriented_rotor_I : oriented_rotor = { rotor = rotor_I'; top_letter = 'A' }
let rotor_II' : rotor = { wiring = rotor_II; turnover = 'B' }
let oriented_rotor_II : oriented_rotor = { rotor = rotor_II'; top_letter = 'A' }
let rotor_III' : rotor = { wiring = rotor_III; turnover = 'B' }

let oriented_rotor_III : oriented_rotor =
  { rotor = rotor_III'; top_letter = 'A' }

let config_ex : config =
  {
    refl = reflector_B;
    rotors = [ oriented_rotor_I; oriented_rotor_II; oriented_rotor_III ];
    plugboard = [];
  }

let config_ex' : config =
  {
    refl = reflector_B;
    rotors =
      [
        oriented_rotor_I;
        oriented_rotor_II;
        { rotor = rotor_III'; top_letter = 'B' };
      ];
    plugboard = [];
  }

let config_ex_step_0 : config =
  {
    refl = reflector_B;
    rotors =
      [
        { rotor = { wiring = rotor_III; turnover = 'V' }; top_letter = 'K' };
        { rotor = { wiring = rotor_II; turnover = 'E' }; top_letter = 'D' };
        { rotor = { wiring = rotor_I; turnover = 'Q' }; top_letter = 'O' };
      ];
    plugboard = [];
  }

let config_ex_step_1 : config =
  {
    refl = reflector_B;
    rotors =
      [
        { rotor = { wiring = rotor_III; turnover = 'V' }; top_letter = 'K' };
        { rotor = { wiring = rotor_II; turnover = 'E' }; top_letter = 'D' };
        { rotor = { wiring = rotor_I; turnover = 'Q' }; top_letter = 'P' };
      ];
    plugboard = [];
  }

let config_ex_step_2 : config =
  {
    refl = reflector_B;
    rotors =
      [
        { rotor = { wiring = rotor_III; turnover = 'V' }; top_letter = 'K' };
        { rotor = { wiring = rotor_II; turnover = 'E' }; top_letter = 'D' };
        { rotor = { wiring = rotor_I; turnover = 'Q' }; top_letter = 'Q' };
      ];
    plugboard = [];
  }

let config_ex_step_3 : config =
  {
    refl = reflector_B;
    rotors =
      [
        { rotor = { wiring = rotor_III; turnover = 'V' }; top_letter = 'K' };
        { rotor = { wiring = rotor_II; turnover = 'E' }; top_letter = 'E' };
        { rotor = { wiring = rotor_I; turnover = 'Q' }; top_letter = 'R' };
      ];
    plugboard = [];
  }

let config_ex_step_4 : config =
  {
    refl = reflector_B;
    rotors =
      [
        { rotor = { wiring = rotor_III; turnover = 'V' }; top_letter = 'L' };
        { rotor = { wiring = rotor_II; turnover = 'E' }; top_letter = 'F' };
        { rotor = { wiring = rotor_I; turnover = 'Q' }; top_letter = 'S' };
      ];
    plugboard = [];
  }

let config_ex_step_5 : config =
  {
    refl = reflector_B;
    rotors =
      [
        { rotor = { wiring = rotor_III; turnover = 'V' }; top_letter = 'L' };
        { rotor = { wiring = rotor_II; turnover = 'E' }; top_letter = 'F' };
        { rotor = { wiring = rotor_I; turnover = 'Q' }; top_letter = 'T' };
      ];
    plugboard = [];
  }

let config_ex_step_4rotors : config =
  {
    refl = reflector_C;
    rotors =
      [
        { rotor = { wiring = rotor_abcd; turnover = 'G' }; top_letter = 'T' };
        { rotor = { wiring = rotor_III; turnover = 'U' }; top_letter = 'I' };
        { rotor = { wiring = rotor_II; turnover = 'A' }; top_letter = 'A' };
        { rotor = { wiring = rotor_I; turnover = 'N' }; top_letter = 'N' };
      ];
    plugboard = [];
  }

let config_ex_step_4rotors' : config =
  {
    refl = reflector_C;
    rotors =
      [
        { rotor = { wiring = rotor_abcd; turnover = 'G' }; top_letter = 'T' };
        { rotor = { wiring = rotor_III; turnover = 'U' }; top_letter = 'J' };
        { rotor = { wiring = rotor_II; turnover = 'A' }; top_letter = 'B' };
        { rotor = { wiring = rotor_I; turnover = 'N' }; top_letter = 'O' };
      ];
    plugboard = [];
  }

let config_cipher : config =
  {
    refl = reflector_B;
    rotors =
      [
        { rotor = { wiring = rotor_I; turnover = 'Q' }; top_letter = 'F' };
        { rotor = { wiring = rotor_II; turnover = 'E' }; top_letter = 'U' };
        { rotor = { wiring = rotor_III; turnover = 'V' }; top_letter = 'N' };
      ];
    plugboard = [ ('A', 'Z') ];
  }

(** [index_test name input expected_output] constructs an OUnit test named
    [name] that asserts the quality of [expected_output] with [index input]. *)
let index_test (name : string) (input : char) (expected_output : int) : test =
  name >:: fun _ ->
  (* the [printer] tells OUnit how to convert the output to a string *)
  assert_equal expected_output (index input) ~printer:string_of_int

(* You will find it helpful to write functions like [index_test] for each of the
   other functions you are testing. They will keep your lists of tests below
   very readable, and will also help you to avoid repeating code. You will also
   find it helpful to create [~printer] functions for the data types in use. *)

let index_tests =
  [
    index_test "index of A is 0" 'A' 0;
    index_test "index of B is 1" 'B' 1;
    index_test "index of Z is 25" 'Z' 25;
    index_test "index of J is 9" 'J' 9;
    index_test "index of K is 25" 'K' 10;
  ]

(* Self-constructed index tests for arguments that breaks precondition *)
let index_test2 (name : string) (input : char) : test =
  name >:: fun _ ->
  assert_raises (Failure "Invalid_arg index") (fun () -> index input)

let index_tests2 =
  [
    index_test2 "index of i raises failure" 'i';
    index_test2 "index of ! raises failure" '!';
    index_test2 "index of @ raises failure" '@';
    index_test2 "index of [ raises failure" '[';
    index_test2 "index of , raises failure" ',';
  ]

(* test for map_r_to_l *)
let map_rl_test (name : string) (wiring : string) (top_letter : char)
    (input_pos : int) (expected_output : int) : test =
  name >:: fun _ ->
  assert_equal expected_output
    (map_r_to_l wiring top_letter input_pos)
    ~printer:string_of_int

let map_rl_tests =
  [
    map_rl_test
      "rl of wiring rotor_abcd and top letter A cause input position 0 to flow \
       to 0"
      rotor_abcd 'A' 0 0;
    map_rl_test
      "rl of wiring rotor_I and top letter A cause input position 0 to flow to \
       4"
      rotor_I 'A' 0 4;
    map_rl_test
      "rl of wiring rotor_bacd and top letter A cause input position 2 to flow \
       to 2"
      rotor_bacd 'A' 2 2;
    map_rl_test
      "rl of wiring rotor_bacd and top letter B cause input position 23 to \
       flow to 23"
      rotor_bacd 'B' 23 23;
    map_rl_test
      "rl of wiring rotor_bacd and top letter C cause input position 24 to \
       flow to 25"
      rotor_bacd 'C' 24 25;
    map_rl_test
      "rl of wiring rotor_I and top letter B cause input position 0 to flow to \
       9"
      rotor_I 'B' 0 9;
    map_rl_test
      "rl of wiring rotor_III and top letter O cause input position 14 to flow \
       to 17"
      rotor_III 'O' 14 17;
  ]

(* test for map_l_to_r *)
let map_lr_test (name : string) (wiring : string) (top_letter : char)
    (input_pos : int) (expected_output : int) : test =
  name >:: fun _ ->
  assert_equal expected_output
    (map_l_to_r wiring top_letter input_pos)
    ~printer:string_of_int

let map_lr_tests =
  [
    map_lr_test
      "lr of wiring rotor_I and top letter A cause input position 0 to flow to \
       20"
      rotor_I 'A' 0 20;
    map_lr_test
      "lr of wiring rotor_I and top letter B cause input position 0 to flow to \
       21"
      rotor_I 'B' 0 21;
    map_lr_test
      "lr of wiring rotor_I and top letter F cause input position 10 to flow \
       to 14"
      rotor_I 'F' 10 14;
    map_lr_test
      "lr of wiring rotor_II and top letter Z cause input position 10 to flow \
       to 2"
      rotor_II 'Z' 10 2;
    map_lr_test
      "lr of wiring rotor_III and top letter J cause input position 11 to flow \
       to 13"
      rotor_III 'J' 11 13;
  ]

(* test for map_refl *)
let map_refl_test (name : string) (wiring : string) (input_pos : int)
    (expected_output : int) : test =
  name >:: fun _ ->
  assert_equal expected_output
    (map_refl wiring input_pos)
    ~printer:string_of_int

let map_refl_tests =
  [
    map_refl_test "refl of rotor_abcd with input pos 23 results in 23"
      rotor_abcd 23 23;
    map_refl_test "refl of reflector_B with input pos 25 results in 19"
      reflector_B 25 19;
    map_refl_test "refl of reflector_B with input pos 24 results in 0"
      reflector_B 24 0;
    map_refl_test "refl of reflector_C with input pos 3 results in 9"
      reflector_C 3 9;
    map_refl_test "refl of reflector_C with input pos 9 results in 3"
      reflector_C 9 3;
  ]

(* test for map_plug *)
let map_plug_test (name : string) (plugs : (char * char) list) (c : char)
    (expected_output : char) : test =
  name >:: fun _ -> assert_equal expected_output (map_plug plugs c)

let map_plug_tests =
  [
    map_plug_test "no cables inserted test X" [] 'X' 'X';
    map_plug_test "cable (A, B) inserted test A" [ ('A', 'B') ] 'A' 'B';
    map_plug_test "cable (A, B) and (C, D) inserted test C"
      [ ('A', 'B'); ('C', 'D') ]
      'C' 'D';
    map_plug_test "cable (D, C) and (B, A) inserted test C"
      [ ('D', 'C'); ('B', 'A') ]
      'C' 'D';
    map_plug_test "all 13 cables inserted test C"
      [
        ('A', 'B');
        ('D', 'Z');
        ('M', 'N');
        ('C', 'E');
        ('F', 'G');
        ('H', 'I');
        ('J', 'K');
        ('L', 'O');
        ('P', 'Q');
        ('R', 'S');
        ('T', 'U');
        ('V', 'W');
        ('X', 'Y');
      ]
      'C' 'E';
  ]

(* test for cipher_char *)
let cipher_char_test (name : string) (config : config) (c : char)
    (expected_output : char) : test =
  name >:: fun _ -> assert_equal expected_output (cipher_char config c)

let cipher_char_tests =
  [
    cipher_char_test "Plugboard empty, lst of rotors empty, reflector_abcd"
      { refl = reflector_abcd; rotors = []; plugboard = [] }
      'A' 'A';
    cipher_char_test
      "Plugboard empty, [oriented_rotor_I; oriented_rotor_II; \
       oriented_rotor_III], reflector_B"
      config_ex 'G' 'P';
    cipher_char_test
      "Plugboard empty, [oriented_rotor_I; oriented_rotor_II; \
       oriented_rotor_III], reflector_B"
      config_ex 'A' 'U';
    cipher_char_test
      "Plugboard empty, [oriented_rotor_I; oriented_rotor_II; \
       oriented_rotor_III], reflector_B"
      config_ex 'B' 'E';
    cipher_char_test
      "Plugboard empty, [oriented_rotor_I; oriented_rotor_II; \
       oriented_rotor_III], reflector_B"
      config_ex 'Z' 'H';
  ]

(* test for step *)
let step_test (name : string) (config : config) (expected_output : config) :
    test =
  name >:: fun _ -> assert_equal expected_output (step config)

let step_tests =
  [
    step_test "config_ex turns into config_ex'" config_ex config_ex';
    step_test "config_ex_step_0 turns into config_ex_step_1" config_ex_step_0
      config_ex_step_1;
    step_test "config_ex_step_1 turns into config_ex_step_2" config_ex_step_1
      config_ex_step_2;
    step_test "config_ex_step_2 turns into config_ex_step_3" config_ex_step_2
      config_ex_step_3;
    step_test "config_ex_step_3 turns into config_ex_step_4" config_ex_step_3
      config_ex_step_4;
    step_test "config_ex_step_4 turns into config_ex_step_5" config_ex_step_4
      config_ex_step_5;
    step_test "special cases of 4 rotors" config_ex_step_4rotors
      config_ex_step_4rotors';
  ]

(* test for cipher *)
let cipher_test (name : string) (config : config) (s : string)
    (expected_output : string) : test =
  name >:: fun _ -> assert_equal expected_output (cipher config s)

let cipher_tests =
  [
    cipher_test "YNGXQ through config_cipher becomes OCAML" config_cipher
      "YNGXQ" "OCAML";
    cipher_test "OCAML through config_cipher becomes YNGXQ" config_cipher
      "OCAML" "YNGXQ";
    cipher_test "TAYLOR through config_cipher becomes VLIUTK" config_cipher
      "TAYLOR" "VLIUTK";
    cipher_test "WANG through config_cipher becomes FLKZ" config_cipher "WANG"
      "FLKZ";
    cipher_test "ILOVEOCAML through config_cipher becomes CAZRHSMBXW"
      config_cipher "ILOVEOCAML" "CAZRHSMBXW";
  ]

let tests =
  "test suite for A1"
  >::: List.flatten
         [
           index_tests;
           index_tests2;
           map_rl_tests;
           map_lr_tests;
           map_refl_tests;
           map_plug_tests;
           cipher_char_tests;
           step_tests;
           cipher_tests;
         ]

let _ = run_test_tt_main tests
