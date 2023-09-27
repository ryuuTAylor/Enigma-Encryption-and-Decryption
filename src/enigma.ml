(************************************************************
   Copyright (C) 2023 Cornell University.
   Created by Justin Hsu (jah659@cornell.edu), Dexter Kozen (dck10@cornell.edu)
   and the CS 3110 course staff.
   You may not redistribute this assignment, distribute any derivatives,
   or use it for commercial purposes.
 ************************************************************)

(** CS 3110 Spring 2023 Assignment A1 Enigma

    @author Taylor Wang (tw492) *)

(************************************************************

  Academic Integrity Statement

  I, the person named in the author comment above, have fully reviewed the
  course academic integrity policies. I have adhered to those policies in
  solving the assignment.

  The policies do permit some limited collaboration among students currently
  enrolled in the course. If I did engage in such collaboration, here is the
  list of other students with whom I collaborated, and a brief summary of that
  collaboration:

  - none I didn't collaborate

  ************************************************************)

(** [index c] is the 0-based index of [c] in the alphabet. Requires: [c] is an
    uppercase letter in A..Z. *)
let index (c : char) : int =
  if int_of_char c < int_of_char 'A' || int_of_char c > int_of_char 'Z' then
    raise (Failure "Invalid_arg index")
  else int_of_char c - int_of_char 'A'

(** Helper Method that is an alternative to mod 26 in this case *)
let mod26 x = if x < 0 then x + 26 else if x <= 25 then x else x - 26

(** [map_r_to_l wiring top_letter input_pos] is the left-hand output position at
    which current would appear when current enters at right-hand input position
    [input_pos] to a rotor whose wiring specification is given by [wiring]. The
    orientation of the rotor is given by [top_letter], which is the top letter
    appearing to the operator in the rotor's present orientation. Requires:
    [wiring] is a valid wiring specification, [top_letter] is in A..Z, and
    [input_pos] is in 0..25. *)
let map_r_to_l (wiring : string) (top_letter : char) (input_pos : int) : int =
  mod26 (index wiring.[mod26 (input_pos + index top_letter)] - index top_letter)

(** Helper Method that is the inverse of the index function I did *)
let invIndex x =
  if x < 0 || x > 25 then raise (Failure "Invalid_arg invIndex")
  else char_of_int (int_of_char 'A' + x)

(** [map_l_to_r] computes the same function as [map_r_to_l], except for current
    flowing left to right. *)
let map_l_to_r (wiring : string) (top_letter : char) (input_pos : int) : int =
  mod26
    (String.index wiring (invIndex (mod26 (input_pos + index top_letter)))
    - index top_letter)

(** [map_refl wiring input_pos] is the output position at which current would
    appear when current enters at input position [input_pos] to a reflector
    whose wiring specification is given by [wiring]. Requires: [wiring] is a
    valid reflector specification, and [input_pos] is in 0..25. *)
let map_refl (wiring : string) (input_pos : int) : int =
  if
    wiring.[map_r_to_l wiring 'A' input_pos] |> index != input_pos
    || input_pos < 0 || input_pos > 25
  then raise (Failure "Invalid_arg map_refl")
  else index wiring.[input_pos]

(** [map_plug plugs c] is the letter to which [c] is transformed by the
    plugboard [plugs]. Requires: [plugs] is a valid plugboard, and [c] is in
    A..Z. *)
let rec map_plug (plugs : (char * char) list) (c : char) =
  match plugs with
  | [] -> c
  | (a, b) :: t -> if a = c then b else if b = c then a else map_plug t c

type rotor = {
  wiring : string;  (** A valid rotor wiring specification. *)
  turnover : char;
      (** The turnover of the rotor, which must be an uppercase letter. This
          field will not be used in the assignment until you implement stepping
          in the excellent scope. *)
}
(** [rotor] represents an Enigma rotor. *)

type oriented_rotor = {
  rotor : rotor;  (** The rotor. *)
  top_letter : char;  (** The top letter showing on the rotor. *)
}
(** [oriented_rotor] represents a rotor that is installed on the spindle hence
    has a top letter. *)

type config = {
  refl : string;  (** A valid reflector wiring specification. *)
  rotors : oriented_rotor list;
      (** The rotors as they are installed on the spindle from left to right.
          There may be any number of elements in this list: 0, 1, 2, 3, 4, 5,
          etc. The order of elements in list represents the order in which the
          rotors are installed on the spindle, **from left to right**. So, the
          head of the list is the leftmost rotor on the spindle, and the last
          element of the list is the rightmost rotor on the spindle. *)
  plugboard : (char * char) list;
      (** A valid plugboard. The order of characters in the pairs does not
          matter, and the order of pairs in the list does not matter. *)
}
(** [config] represents the configuration of an Enigma machine. *)

(** Factor out two methods *)
let rec factor f1 (rotors : oriented_rotor list) (input_pos : int) =
  match rotors with
  | [] -> input_pos
  | h :: t -> factor f1 t (f1 h.rotor.wiring h.top_letter input_pos)

(** Helper method that helps solve a list of rotors from right to left *)
let rec map_rotors_r_to_l = factor map_r_to_l

(** Helper method that helps solve a list of rotors from left to right *)
let rec map_rotors_l_to_r = factor map_l_to_r

(** [cipher_char config c] is the letter to which the Enigma machine ciphers
    input [c] when it is in configuration [config]. Requires: [config] is a
    valid configuration, and [c] is in A..Z. *)
let cipher_char (config : config) (c : char) : char =
  map_plug config.plugboard
    (invIndex
       (map_rotors_l_to_r config.rotors
          (map_refl config.refl
             (map_rotors_r_to_l (List.rev config.rotors)
                (index (map_plug config.plugboard c))))))

(** Helper Method that changes 1 to the top letter of an oriented rotor *)
let change1 (orotor : oriented_rotor) : oriented_rotor =
  {
    rotor = orotor.rotor;
    top_letter = index orotor.top_letter + 1 |> mod26 |> invIndex;
  }

(** Helper Method that returns a bool whether an oriented rotor has its top
    letter equal to its turnover *)
let turn (orotor : oriented_rotor) : bool =
  orotor.top_letter == orotor.rotor.turnover

(** Helper Method that helps complete all other not_leftmost_rotor rotors'
    steppings recursively. Mustbe an unempty list input *)
let rec steps (orotors : oriented_rotor list) : oriented_rotor list =
  match orotors with
  | [ l ] -> [ change1 l ]
  | l1 :: l2 :: l3 ->
      if turn l1 || turn l2 then change1 l1 :: steps (l2 :: l3)
      else l1 :: steps (l2 :: l3)
  | _ -> raise (Failure "Invalid_arg steps")

(** [step config] is the new configuration to which the Enigma machine
    transitions when it steps beginning in configuration [config]. Requires:
    [config] is a valid configuration. *)
let step (config : config) : config =
  {
    refl = config.refl;
    rotors =
      (match config.rotors with
      | [] -> []
      | [ l ] -> [ change1 l ]
      | l1 :: l2 :: l3 ->
          (if turn l2 then change1 l1 else l1) :: steps (l2 :: l3));
    plugboard = config.plugboard;
  }

(** [cipher config s] is the string to which [s] enciphers when the Enigma
    machine begins in configuration [config]. Requires: [config] is a valid
    configuration, and [s] contains only uppercase letters. *)
let rec cipher (config : config) (s : string) : string =
  if String.length s = 0 then ""
  else
    String.cat
      (String.make 1 (cipher_char (step config) s.[0]))
      (cipher (step config) (String.sub s 1 (String.length s - 1)))

let hours_worked = 15
