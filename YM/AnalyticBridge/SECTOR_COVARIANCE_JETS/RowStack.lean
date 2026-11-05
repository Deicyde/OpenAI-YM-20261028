import YM.AnalyticBridge.SECTOR_COVARIANCE_JETS.Due

set_option warningAsError false

/-! Absolute dues on actual affine component stacks including path ancestry
(PathData itself an input exactly as in `committed`). -/

set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.Covariance
open Function Filter Lattice Wilson RG Precision Exterior Tree Matrix Pressure
  Pressure.Tube Pressure.Stores Bid Next.Fluctuations Next.SectorChange Next.SectorChange.Rows
  Next.SectorChange.Wisps Push.SectorMeasure FreeResolvent.Mark FreeResolvent.TestD
open FreeResolvent.Affine (Ceiling)
open scoped Topology Matrix.Norms.Frobenius ContDiff InnerProductSpace BigOperators Classical

variable {G : Gauge} {c f : Side} {S : StepData c f} {k : ℕ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {σ δ l : ℝ}

/-- A telescope at the *actual* real branch priced via surrogate globally
extended kernels (used only for calculus proof). Keep stronger Bills even when
each summation is infinite at a single physical endpoint. -/
lemma stack {o y : Site c} {B : Directions G c} (v : ℕ → Directions G c → E)
    {p q : ℕ → ℝ} (hp : ∀ i, 0 ≤ p i) (hC : ∀ i, Ceiling k (p i) (v i)) (ht : ∀ i, Due σ o y k (q i) (v i) B)
    (hP : Summable p) (hQ : Summable q) :
    Due σ o y k (∑' i,q i) (fun x => ∑' i,v i x) B := by
  let m : ℕ → ℕ → ℝ := fun _ => p
  have hm (j : ℕ) (_ : (j : ℕ∞) ≤ (k : ℕ)) : Summable (m j) := hP
  have hf i : ContDiff ℝ ((k:ℕ∞):ℕ∞ω) (v i) := (hC i).smooth
  have hc (j i : ℕ) x (e : (j:ℕ∞) ≤ (k:ℕ)) : ‖iteratedFDeriv ℝ j (v i) x‖ ≤ m j i :=
    (hC i).op j x (by exact_mod_cast e)
  let f x := ∑' i,v i x
  have hh (l : List (Atom G c)) (hl : l.length ≤ k) :
      HasSum (fun i => jet atom (v i) l B) (jet atom f l B) := by
    have he : (l.length:ℕ∞) ≤ (k:ℕ∞) := by exact_mod_cast hl
    have hh : HasSum (fun i => iteratedFDeriv ℝ l.length (v i) B) (iteratedFDeriv ℝ l.length f B) := by
      rw [show f=_ from rfl,iteratedFDeriv_tsum_apply hf hm hc he B]
      exact (Summable.of_norm_bounded hP (fun i => hc l.length i B he)).hasSum
    let L := ContinuousMultilinearMap.apply ℝ (fun _ : Fin l.length => Directions G c) E (atom ∘ l.get)
    exact L.hasSum hh
  have hv a b (l : List (Atom G c)) (hl : l.length ≤ k) (h : ∀ i, (meterMark G c σ).pay l a *
        ((FreeResolvent.native c).weight σ a b * ‖jet atom (v i) l B‖) ≤ q i) :
      (meterMark G c σ).pay l a * ((FreeResolvent.native c).weight σ a b * ‖jet atom f l B‖) ≤ ∑' i,q i := by
    let D := (meterMark G c σ).pay l a
    let C := (FreeResolvent.native c).weight σ a b
    have hd : 0 ≤ D := (pay_pos ..).le
    have hc : 0 ≤ C := (FreeResolvent.native c).weight_nn ..
    let w i := jet atom (v i) l B
    have hw : Summable (fun i => ‖w i‖) := Summable.of_nonneg_of_le (fun i => norm_nonneg _) (fun i =>
        ((hC i).bill (hp i) atom atom_small l hl _)) hP
    rw [← (hh l hl).tsum_eq]
    apply le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm hw) hc) hd)
    rw [← tsum_mul_left,← tsum_mul_left]
    exact Summable.tsum_le_tsum h ((hw.mul_left C).mul_left D) hQ
  constructor
  · exact (contDiff_tsum hf hm hc).contDiffAt
  · intro l hl; exact hv o y l hl fun i => (ht i).row l hl
  intro l hl; exact hv y o l hl fun i => (ht i).col l hl

def history (S : StepData c f) (s : Signed) (i : Cell f) (W : PathData G) (x : ℝ) (V : Config G c)
    (j : Atom G f) (n : ℕ) (B : Directions G c) :=
  let p := W.row i.2 n
  if p.2.length ≤ till x then p.1 • line S s V j i.1 p.2 B else 0

lemma settles (S : StepData c f) (s : Signed) (i : Twin f) (hi : i.2=true) (T : Tube G S) (x : ℝ)
    (V : Config G c) (j : Atom G f) (B : Directions G c) (hB : ‖B‖ ≤ 1) :
    faceKick T x (increment V B) (atom j) s i = ∑' n, history S s i.1 T.up x V j n B := by
  unfold faceKick barrel history; rw [if_pos hi]; apply tsum_congr
  intro n; dsimp only; split
  next h => rw [line_agrees S s V j i.1.1 _ hB]; rfl
  rfl

lemma ascension (S : StepData c f) (s : Signed) (T : Tube G S) {P : Teller G} (h : P.Funds S T)
    (x : ℝ) (V : Config G c) (i : Twin f) (hi : i.2=true) (j : Atom G f) (B : Directions G c)
    (k : ℕ) (hd : 0≤δ) (he : (1+2*k)*δ ≤ P.top.width/2) (hp : ‖B‖<1) :
    Due δ (s.act (S.ratio.parent i.1.1)) (S.ratio.parent j.1.1) k (P.top.paths*flight G P.top.width δ k)
      (fun b => faceKick T x (increment V b) (atom j) s i) B := by
  let v := history S s i.1 T.up x V j
  let Z (n : ℕ) := T.up.row i.1.2 n
  let σ := P.top.width
  let m (n : ℕ) := |(Z n).1| * Real.exp (σ*(Z n).2.length)
  have hm n : 0 ≤ m n := mul_nonneg (abs_nonneg _) (Real.exp_pos _).le
  obtain ⟨μ,g,hμ,-⟩ := h.feeds
  obtain ⟨-,hh,hq⟩ := hμ.rows i.1.2
  let L := lineMoney G k σ; let C := flight G σ δ k
  let p (n : ℕ) := m n*L; let q (n : ℕ) := m n*C
  have ht n : Ceiling k (p n) (v n) := by
    let a := Z n
    by_cases hx : a.2.length ≤ till x
    · have hy : v n = fun b => a.1 • line S s V j i.1.1 a.2 b := funext fun _ => if_pos hx
      rw [hy]; apply ((line_cap _ _ _ _ _ _ _ P.top.width_pos).scale _).mono
      unfold p m L a σ; rw [Real.norm_eq_abs]; exact le_of_eq (by ring)
    rw [show v n = fun _ => 0 from funext fun _ => if_neg hx]; apply (Ceiling.ceiling_const _).mono
    rw [norm_zero]; exact mul_nonneg (hm _) (lineMoney_nn ..)
  let o := s.act (S.ratio.parent i.1.1); let z := S.ratio.parent j.1.1
  have hr i' : Due δ o z k (q i') (v i') B := by
    let a := Z i'
    by_cases hx : a.2.length ≤ till x
    · have hy : v i' = fun b => a.1 • line S s V j i.1.1 a.2 b := funext fun _ => if_pos hx
      rw [hy]; apply Due.weaken (Due.scale (linePrice _ _ _ _ _ _ B k hp P.top.width_pos hd he)
        (mul_nonneg (Real.exp_pos _).le (flight_nn ..)) _) -- then inequality
      unfold q m C σ a; rw [Real.norm_eq_abs]; exact (mul_assoc ..).ge
    rw [show v i'=0 from funext fun _ => if_neg hx]; exact Due.funded_zero (mul_nonneg (hm _) (flight_nn ..))
  have hw := stack v (fun i => mul_nonneg (hm i) (lineMoney_nn ..)) ht hr ((show Summable m from hh).mul_right L) (hh.mul_right C)
  refine (hw.weaken ?_).congr_germ ((normEventually hp).mono fun b hu => settles S s i hi T x V j b hu)
  unfold q; rw [tsum_mul_right]; exact mul_le_mul_of_nonneg_right hq (flight_nn ..)

def faceMoney (P : Teller G) (δ : ℝ) (k : ℕ) :=
  max (Real.sqrt P.top.clip.direct * (Real.exp ((1+2*k)*δ*(5:ℕ)) * bladeMoney G (k+1)))
    (P.top.paths*flight G P.top.width δ k)
lemma faceMoney_nn (P : Teller G) (δ : ℝ) (k : ℕ) : 0 ≤ faceMoney P δ k :=
  (le_max_of_le_left (mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg (Real.exp_pos _).le (blade_nn ..))))

/-- D-face dues. θ-address multiplication (slip channel and restricting and
reading color) is later, this bound uniform across every channel/geometry. -/
lemma face_payment (S : StepData c f) (s : Signed) (T : Tube G S) {P : Teller G} (h : P.Funds S T)
    (x : ℝ) (V : Config G c) (i : Twin f) (j : Atom G f) (B : Directions G c)
    (k : ℕ) (hd : 0≤δ) (he : (1+2*k)*δ ≤ P.top.width/2) (hp : ‖B‖<1) :
    Due δ (s.act (S.ratio.parent i.1.1)) (S.ratio.parent j.1.1) k (faceMoney P δ k)
      (fun b => faceKick T x (increment V b) (atom j) s i) B := by
  by_cases hi : i.2=true
  · exact Due.weaken (ascension S s T h x V i hi j B k hd he hp) (le_max_right ..)
  unfold faceKick; simp_rw [if_neg hi,h.high]
  refine Due.congr_germ (v:=fun b => Real.sqrt P.top.clip.direct • gray S s i.1 V j b) ?_ ?_
  · have he := Due.scale (grayPrice S s V j i.1 B k hp hd) (mul_nonneg (Real.exp_pos _).le (blade_nn ..)) (Real.sqrt P.top.clip.direct)
    rw [Real.norm_of_nonneg (Real.sqrt_nonneg _)] at he
    exact he.weaken (le_max_left ..)
  filter_upwards [normEventually hp] with b hb
  rw [gray_agrees S s _ V j hb]
end YM.AnalyticBridge.Covariance
