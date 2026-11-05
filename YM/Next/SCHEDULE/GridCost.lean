import YM.Bid.Corners
import YM.Next.SCHEDULE.Pre
import YM.Work.G07.Stencil

/-!
# Cost of any number of derivatives on the TRANSPORT path

Schedule prerequisite for E path hits. All matrices in physical unitary
representation with Frobenius. Orders can be large *arbitrary pre-L* orders.
Keep actual slot word, incl inverse physical orientation and repeated links.
Polynomial growth PER fixed order not length-exponential! (Naive product
norm not this; R0 relaxation might buy a very small exponential).
Constant lanes isolate unitarity. Reuse existing stencil differentiation
library (G07), but path-length budget here essential when summing infinitely
many labels.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Scheduling.Wages
open Work.G07 Lattice RG Wilson
open scoped ContDiff Matrix.Norms.Frobenius BigOperators

variable {G : Gauge} {n : Side}

-- auxiliary word with fixed-matrix letters
inductive Piece (G : Gauge) (n : Side)
| push (i : Edge (Site n))
| pull (i : Edge (Site n))
| mat (x : G.Mat)
abbrev Trail (G : Gauge) (n : Side) := List (Piece G n)

namespace Piece
def call : Piece G n → Config G n → G.Mat
  | push i,U => G.mat (U i)
  | pull i,U => G.mat (U i)⁻¹
  | mat x,_ => x

theorem soft (p : Piece G n) (k : ℕ) : LeftSmooth k p.call := by
  cases p with
  | push i => exact smooth_link i
  | pull i => exact (smooth_link i).postcomp (starL' ℝ).toContinuousLinearMap
  | mat x =>
    apply (LeftBound.const (E:=G.Mat) (k:=k) (D:=fun _ => True) (Z:=fun _ => True) zero_le_one x).smooth

def size : Piece G n → ℝ
  | mat x => ‖x‖
  | _ => 1

def links : Piece G n → List (Edge (Site n))
  | push i => [i]
  | pull i => [i]
  | mat _ => []
end Piece

-- Trail metrics
namespace Path

def eval : Trail G n → Config G n → G.Mat
  | [],_ => 1
  | a::l,U => a.call U * eval l U

def price : Trail G n → ℝ
  | [] => 1
  | a::l => a.size*price l

def uses : Trail G n → List (Edge (Site n))
  | [] => []
  | a::l => a.links ++ uses l

lemma pos (l : Trail G n) : 0 ≤ price l := by
  induction l with
  | nil => exact zero_le_one
  | cons a l ih => cases a <;> first | exact mul_nonneg zero_le_one ih | exact mul_nonneg (norm_nonneg _) ih

lemma scale (l : Trail G n) (U : Config G n) : ‖eval l U‖ ≤ price l*‖(1:G.Mat)‖ := by
  induction l with
  | nil => simp only [eval,price,one_mul,le_refl]
  | cons a l ih =>
    rw [eval]; cases a with
    | push i => rw [Piece.call,Gauge.mul_frob_eq (G.mat (U i)) _ (G.mat_star_mul (U i))]; simpa only [price,Piece.size,one_mul] using ih
    | pull i => rw [Piece.call,Gauge.mul_frob_eq (G.mat (U i)⁻¹) _ (G.mat_star_mul (U i)⁻¹)]; simpa only [price,Piece.size,one_mul] using ih
    | mat x => rw [Piece.call]; apply (norm_mul_le ..).trans; calc
        _ ≤ _ := mul_le_mul_of_nonneg_left ih (norm_nonneg x)
        _ = _ := (mul_assoc ..).symm

lemma soft (l : Trail G n) (k : ℕ) : LeftSmooth k (eval l) := by
  induction l with
  | nil => intro l hl U; simp only [eval,left_const]; exact contDiff_const
  | cons a l ih => exact (a.soft k).mul ih

/-- Insert differentiated generators into the *actual* product; positions
remain positive-link indices. -/
def changeBy (A : Directions G n) : Trail G n → List (Trail G n)
  | [] => []
  | a::l =>
    let tail := (changeBy A l).map (fun l' => a::l')
    match a with
    | .push i => (Piece.mat (G.colorMat (A i))::a::l)::tail
    | .pull i => (a::Piece.mat (-(G.colorMat (A i)))::l)::tail
    | .mat _ => tail

def group (H : List (Trail G n)) (U : Config G n) := (H.map (eval · U)).sum

theorem head (a : Piece G n) (l : List (Trail G n)) (U) :
    group (l.map (fun l' => a::l')) U = a.call U*group l U := by
  induction l with
  | nil => simp [group]
  | cons v l ih => unfold group at *; simp only [List.map_cons,List.sum_cons,eval,ih,mul_add]

private lemma fwd (i : Edge (Site n)) (A : Directions G n) (U : Config G n) :
    leftDerivs (Piece.push i).call [A] U = G.colorMat (A i) * G.mat (U i) := by
  change leftDerivs (fun V : Config G n => G.mat (V i)) _ _=_; simpa [linkPrefix] using left_link i [A] U

private lemma bwd (i : Edge (Site n)) (A : Directions G n) (U : Config G n) :
    leftDerivs (Piece.pull i).call [A] U = G.mat (U i)⁻¹ * -(G.colorMat (A i)) := by
  have h := left_linear (smooth_link (k:=1) i) (starL' ℝ (A:=G.Mat)).toContinuousLinearMap (l:=[A]) (by simp)
  have hh : leftDerivs (Piece.pull i).call [A] U = star (leftDerivs (Piece.push i).call [A] U) := congr_fun h U
  rw [hh, fwd, star_mul,G.colorMat_skew]; rfl

theorem first (l : Trail G n) (A : Directions G n) : leftDerivs (eval l) [A] = group (changeBy A l) := by
  induction l with
  | nil => funext U; simp [eval,group,changeBy,left_const]
  | cons a l ih =>
    funext U
    rw [show eval (a::l) = fun U => a.call U* eval l U from rfl, left_first_mul (a.soft 1) (soft l 1) A, ih]
    dsimp only
    have hh (l : List (Trail G n)) (w) : group (w::l) U=eval w U+group l U:=by simp [group]
    cases a with
    | mat x => rw [show (Piece.mat (n:=n) x).call = fun _ => x from rfl,left_const]; simp [changeBy,head,Piece.call]
    | push i => rw [fwd,changeBy, hh,head]; simp only [Piece.call, eval, mul_assoc]
    | pull i => rw [bwd,changeBy, hh,head]; simp only [Piece.call, eval, mul_assoc]

theorem cost (A : Directions G n) (T : ℝ) (l : Trail G n)
    (h : ∀ i ∈ uses l, ‖G.colorMat (A i)‖ ≤ T) :
    (changeBy A l).length=(uses l).length ∧ ∀ q∈changeBy A l, uses q=uses l ∧ price q ≤ price l*T := by
  induction l with
  | nil => simp [changeBy,uses]
  | cons a l ih =>
    obtain ⟨hl, ih⟩:= ih (fun i hi => h i (by unfold uses; exact List.mem_append_right _ hi))
    have ht : ∀ q∈(changeBy A l).map (fun l' => a::l'), uses q=uses (a::l) ∧ price q ≤ price (a::l)*T := by
      rintro q h
      obtain ⟨v,hv,rfl⟩:=List.mem_map.mp h
      obtain ⟨hx,hP⟩:=ih v hv
      refine ⟨by rw [uses,uses,hx], ?_⟩
      have hb : 0≤a.size:= by cases a <;> first | exact zero_le_one | exact norm_nonneg _
      rw [price,price,mul_assoc]; exact mul_le_mul_of_nonneg_left hP hb
    cases a with
    | mat X => exact ⟨by simp only [changeBy,uses,Piece.links,List.length_map,hl,List.nil_append],ht⟩
    | push i =>
      refine ⟨by simp [changeBy,uses,Piece.links,hl],fun q hh => (List.mem_cons.mp hh).elim ?_ (ht q)⟩
      rintro rfl
      have hi:=h i (by unfold uses Piece.links; simp)
      refine ⟨by simp [uses,Piece.links],?_⟩
      apply le_trans _ (mul_comm ..).ge
      exact mul_le_mul_of_nonneg_right hi (Path.pos _)
    | pull i =>
      refine ⟨by simp [changeBy,uses,Piece.links,hl],fun q hh => (List.mem_cons.mp hh).elim ?_ (ht q)⟩
      rintro rfl; refine ⟨by simp [uses,Piece.links],?_⟩
      have hi:=h i (by unfold uses Piece.links; simp)
      simp only [price,Piece.size,one_mul,norm_neg]
      rw [mul_comm (price l)]
      exact mul_le_mul_of_nonneg_right hi (Path.pos _)

private lemma split_derivative (A : List (Directions G n)) (H : List (Trail G n)) :
    LeftSmooth A.length (group H) ∧ ∀ U, leftDerivs (group H) A U = (H.map (fun i => leftDerivs (eval i) A U)).sum := by
  induction H with
  | nil =>
    have h : group [] = fun (_ : Config G n) => (0 : G.Mat) := by funext _; simp [group]
    rw [h]; exact ⟨(LeftBound.const (k:=A.length) (D:=fun _ => True) (Z:=fun _ => True) zero_le_one (0:G.Mat)).smooth,
      fun _ => by simp [left_const]⟩
  | cons i H ih =>
    rw [show group (i::H) = fun U => eval i U+group H U by ext; simp [group]]
    refine ⟨(soft i _).add ih.1,fun U => ?_⟩
    simp only [left_add (soft i A.length) ih.1 (le_refl A.length),List.map_cons,List.sum_cons, ih.2]

private lemma norm_collect (W : List (Trail G n)) (f : Trail G n → G.Mat) (c : ℝ)
    (h : ∀ i∈W,‖f i‖ ≤ c) : ‖(W.map f).sum‖ ≤ W.length*c := by
  induction W with
  | nil => simp
  | cons i W ih =>
    rw [List.map_cons,List.sum_cons,List.length_cons,Nat.cast_add_one,add_mul,one_mul,add_comm _ c]
    exact le_trans (norm_add_le ..) (add_le_add (h i List.mem_cons_self) (ih (fun j hj => h j (List.mem_cons_of_mem _ hj))))

theorem bill (l : Trail G n) (T : ℝ) (ht : 0 ≤ T) (U : Config G n) (A : List (Directions G n))
    (h : ∀ i∈uses l,∀ a∈A, ‖G.colorMat (a i)‖ ≤ T) :
    ‖leftDerivs (eval l) A U‖ ≤ (price l*‖(1:G.Mat)‖)*(T*(uses l).length)^A.length := by
  induction A using List.reverseRecOn generalizing l with
  | nil => simpa only [leftDerivs,List.length_nil,pow_zero,mul_one] using scale l U
  | append_singleton A t ih =>
    rw [left_append,first,(split_derivative ..).2 U]
    have he := cost t T l (fun i hi => h i hi t (by simp))
    apply (norm_collect (changeBy t l) _ ((price l*T*‖(1:G.Mat)‖)*(T*(uses l).length)^A.length) ?_).trans ?_
    · intro i hi
      obtain ⟨hx,hp⟩:=he.2 i hi
      apply le_trans <| ih i (fun j hj a ha => h j (hx ▸ hj) a (List.mem_append_left _ ha))
      rw [hx]; gcongr
    rw [he.1,List.length_append,List.length_singleton,pow_succ]; apply le_of_eq; ring
end Path
end YM.Next.Scheduling.Wages
