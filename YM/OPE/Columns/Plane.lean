import YM.OPE.Columns.Cone
import YM.OPE.Rough.Factory

/-! # Multi-level triangular transmission -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Columns
open Set Function Filter RG Wilson Lattice MergeProof Labels Source PhysicalNext.Repeat.Legato.Bandage
open Push.Local Work.G08 Extra.Histories
open scoped Topology BigOperators
variable {G : Gauge} {C : Family G} {W r D} (T : TableTickets C W r D)
  {d N p k e : ℕ}
set_option quotPrecheck false
local notation "F" => C.labels.level d
local notation "K" => (C.factory d N p)
local notation "U" => C.ref d
local notation "B" => C.label d
local notation "P" => low F e
local notation "μ" => (F).coeffSize

/-- Bare vector, read at level k (use `readTerminal` for the physical normalization). -/
def trace (C : Family G) (d N p k : ℕ) (x : C.label d) := ((C.factory d N p).entries k x).x
set_option quotPrecheck false
local notation "Tr" => trace C d N p
local notation "ζ" => fun k => (C.path.levels.params k).columns

lemma readTerminal (h : C.Makes) (hk : C.ref d ≤ N) (x : B) :
    Tr U x = (K).terminal x := (h.calibrated d N p hk).reads x

variable  (h : C.Makes)
include h
lemma linTrace (hk : U ≤ k) (hn : k ≤ N) : IsLinearMap ℂ (Tr k) :=
  ((h.calibrated d N p (hk.trans hn)).linear k hk hn).1

include T
lemma entire_cone {x : C.label d} (hx : P x=x) (he : e < d) (hk : U ≤ k) (hn : k ≤ N) :
    μ (Tr k x) ≤ (ζ) k * μ (P (Tr k x)) := by
  induction hn using Nat.decreasingInduction with
  | self =>
    rw [show Tr N x=x from (h.calibrated d N p hk).bare_coord x,hx]; exact le_mul_of_one_le_left
      (size_nonneg _ _) (C.path.levels.params N).columns_ge
  | of_succ i hi ih => exact (step_expand T.system.costs.cost T.system.costs.back
      (T.columns d N p (hk.trans hi.le) i hk hi) x (ih (hk.trans i.le_succ)) he).1

omit h T in
/-- full prefix product (rather than optimizing in both endpoints) -/
def juice (H : Levels G) (n : ℕ) := ∏ i ∈ Finset.range n, (H.params (i+1)).columns
local notation "J" => juice C.path.levels
omit h T in
lemma juice_pos (H : Levels G) (n : ℕ) : 1 ≤ juice H n := Finset.one_le_prod fun i _ =>
  (H.params (i+1)).columns_ge
omit h T in
lemma juice_step (H : Levels G) (i) : juice H (i+1) = (H.params (i+1)).columns*juice H i := by
  rw [mul_comm]; exact Finset.prod_range_succ _ _
local notation "α" => C.S.a
lemma bare_comp {x : C.label d} (hx : P x=x) (he : e<d) (hk : U ≤ k) (hn : k ≤ N) :
    (J k) * (((α) k / (α) N)^(d-e) * μ x) ≤ (J N) * μ (P (Tr k x)) := by
  induction hn using Nat.decreasingInduction with
  | self => rw [div_self (C.S.a_pos N).ne',one_pow,one_mul,show Tr N x=x from (h.calibrated d N p hk).bare_coord x,hx]
  | of_succ i hi ih =>
    let L : ℝ:= (C.S.block i).val
    have hl : 0 < L := by unfold L; positivity
    let a := Tr (i+1) x; let b := Tr i x; let s := (ζ) (i+1); let t := d-e
    have hg : L^t * μ (P a) ≤ s * μ (P b) := (step_expand T.system.costs.cost T.system.costs.back
      (T.columns d N p (hk.trans hi.le) i hk hi) x (entire_cone (p:=p) T h hx he (hk.trans i.le_succ) hi) he).2
    have hf := juice_pos C.path.levels N
    have heq : C.S.a i = L*C.S.a (i+1) := by rw [Schedule.a_step, mul_div_cancel₀ _ hl.ne']
    specialize ih (hk.trans i.le_succ); rw [heq,mul_div_assoc, mul_pow]
    apply le_of_mul_le_mul_left (a:=s) _ (zero_lt_one.trans_le (C.path.levels.params (i+1)).columns_ge)
    calc
       _ = L^t*(J (i+1)*(((α) (i+1)/(α) N)^t * μ x)) := by rw [juice_step]; unfold s t; ring
       _ ≤ L^t*(J N*μ (P a)) := mul_le_mul_of_nonneg_left ih (by positivity)
       _ ≤ _ := by linarith only [mul_le_mul_of_nonneg_left hg (zero_le_one.trans hf)] -- b, s

lemma top_shrunk {x : C.label d} (hx : P x=x) (he : e<d) (hk : U ≤ k) (hn : k ≤ N) :
    ((α) k/(α) N)^(d-e)* μ x ≤ (J N)* μ (Tr k x) := calc
  _ ≤ (J k)*(((α) k / (α) N)^(d-e) * μ x) := le_mul_of_one_le_left (mul_nonneg
    (pow_nonneg (div_nonneg (C.S.a_pos _).le (C.S.a_pos _).le) _) (size_nonneg F _)) (juice_pos ..)
  _ ≤ _ := (bare_comp T h hx he hk hn).trans (mul_le_mul_of_nonneg_left (size_low ..)
    (zero_le_one.trans (juice_pos ..)))
lemma reaches (y : B) (he : e<d) (hk : U ≤ k) (hn : k ≤ N) :
    ∃ x : B, P x = x ∧ P (Tr k x) = P y := by
  let M := LinearMap.range P
  have hp(u:M) : P u.val=u.val := by
    obtain ⟨z,s,hz⟩:= u; change P z=z; rw [← hz]; exact project ..
  let f := (P).rangeRestrict.comp (((linTrace (p:=p) h hk hn).mk' (Tr k)).comp M.subtype)
  have hf : Surjective f := LinearMap.injective_iff_surjective.mp (LinearMap.ker_eq_bot.mp
    (LinearMap.ker_eq_bot'.mpr (fun u hu => ?_)))
  · obtain ⟨x,hx⟩ := hf ((P).rangeRestrict y); exact ⟨x.val,hp x, congr_arg Subtype.val hx⟩
  have he' : P (Tr k u.val)=0:= congr_arg Subtype.val hu
  have ht := bare_comp (p:=p) T h (hp u) he hk hn
  rw [he'] at ht
  have ha : 0 < (J k)*((α) k/(α) N)^(d-e) := mul_pos (zero_lt_one.trans_le (juice_pos ..))
    (pow_pos (div_pos (C.S.a_pos _) (C.S.a_pos _)) _)
  apply Subtype.ext; apply size_separates F u.val; apply nonpos_of_mul_nonpos_right _ ha
  rw [mul_assoc]; exact le_trans ht (by simp [Frame.coeffSize])

/-- Subtract a representative from the plane at k; no period dependence in the
multiplier. -/
lemma cancel (y : B) (he : e<d) (hk : U ≤ k) (hn : k ≤ N) :
    ∃ x : B, P x = x ∧ P (Tr k (y-x))=0 ∧
      μ (Tr k (y-x)) ≤ (1+(ζ) k)* μ (Tr k y) := by
  obtain ⟨x,hx,hr⟩ := reaches (p:=p) T h (Tr k y) he hk hn
  have ht := entire_cone T h hx he hk (p:=p) hn; rw [hr] at ht
  refine ⟨x,hx,?_⟩
  have hy : Tr k (y-x)=Tr k y - Tr k x := ((linTrace h hk hn).mk' (Tr k)).map_sub y x
  rw [hy]
  refine ⟨by rw [map_sub,hr,sub_self], (size_sub _ _ _).trans ?_⟩
  rw [add_mul,one_mul]
  exact add_le_add le_rfl (ht.trans (mul_le_mul_of_nonneg_left (size_low ..) (zero_le_one.trans (C.path.levels.params k).columns_ge)))

/-- Bound the quotient evolution. Pays also for plane-representative subtraction
at the *destination*; permissible charges at neighbor indices. -/
lemma quotient_step (y : B) (he : e<d) (hk : U ≤ k) (hn : k < N) (hx : P (Tr (k+1) y)=0) :
    ∃ x : B, P x=x ∧ P (Tr k (y-x))=0 ∧
      μ (Tr k (y-x)) ≤ (1+(ζ) k)*(ζ) (k+1) *((C.S.block k).val:ℝ)^(d-(e+1))* μ (Tr (k+1) y) := by
  have hg:= step_transverse T.system.costs.cost T.system.costs.back
     (T.columns d N p (hk.trans hn.le) k hk hn) y hx
  obtain ⟨x,hx,ht,hT⟩:=cancel (p:=p) T h y he hk hn.le
  refine ⟨x,hx,ht,hT.trans ((mul_le_mul_of_nonneg_left hg ?_).trans_eq ?_)⟩
  · exact add_nonneg zero_le_one (zero_le_one.trans (C.path.levels.params k).columns_ge)
  simp only [mul_assoc]; rfl

omit T h in
def gel (H : Levels G) (m : ℕ) := ∏ i ∈ Finset.range m, (1+(H.params i).columns)*(H.params (i+1)).columns
local notation "q" => gel C.path.levels
omit T h in
lemma gel_pos (H : Levels G) (m : ℕ) : 1 ≤ gel H m := Finset.one_le_prod fun i _ => one_le_mul_of_one_le_of_one_le
  (le_add_of_nonneg_right (zero_le_one.trans (H.params i).columns_ge)) (H.params (i+1)).columns_ge
omit T h in
lemma gel_step (H : Levels G) (m) : gel H (m+1) = gel H m*((1+(H.params m).columns)*(H.params (m+1)).columns) := by
  exact Finset.prod_range_succ _ _
variable {j : ℕ}
lemma quotient_between (y : B) (he : e<d) (hk : U ≤ k) (hj : k ≤ j) (hn : j ≤ N) (hx : P (Tr j y)=0) :
    ∃ x : B, P x=x ∧ P (Tr k (y-x))=0 ∧
      q k * μ (Tr k (y-x)) ≤ q j * ((α) k / (α) j)^(d-(e+1)) * μ (Tr j y) := by
  induction hj using Nat.decreasingInduction generalizing y with
  | self => exact ⟨0, map_zero P, by rwa [sub_zero], by rw [div_self (C.S.a_pos j).ne',one_pow,mul_one,sub_zero]⟩
  | of_succ i hi ih =>
    obtain ⟨x,hx,hP,hL⟩ := ih y (hk.trans i.le_succ) hx
    obtain ⟨u,hu,hS,hM⟩ := quotient_step T h (y-x) he hk (hi.trans_le hn) hP
    let L : ℝ:= (C.S.block i).val; have hp : 0 < L := by unfold L; positivity
    let t := d-(e+1)
    let s := Tr j y
    refine ⟨x+u,by rw [map_add,hx,hu],?_⟩
    rw [← sub_sub]; refine ⟨hS,?_⟩
    have hv : C.S.a i = L*C.S.a (i+1) := by rw [Schedule.a_step,mul_div_cancel₀ _ hp.ne']
    calc
       _ ≤ _ := mul_le_mul_of_nonneg_left hM (zero_le_one.trans (gel_pos ..))
       _ = L^t*(q (i+1)*μ (Tr (i+1) (y-x))) := by rw [gel_step]; unfold L t; ring
       _ ≤ L^t*(q j*((α) (i+1)/(α) j)^t * μ s) := mul_le_mul_of_nonneg_left hL (pow_pos hp t).le
       _ = _ := by rw [hv,mul_div_assoc,mul_pow]; unfold t s; ring

lemma quotient_issue (y : B) (he : e<d) (hk : U ≤ k) (hn : k ≤ N) :
    ∃ x : B, P x=x ∧ μ ((K).terminal (y-x)) ≤
      q k * (1+(ζ) k)* ((α) U / (α) k)^(d-(e+1)) * μ (Tr k y) := by
  obtain ⟨x,hx,hP,hL⟩ := cancel (p:=p) T h y he hk hn
  obtain ⟨u,hu,hS,hM⟩ := quotient_between T h (y-x) he le_rfl hk hn hP
  let t := d-(e+1)
  have hz : 0 ≤ q k * ((α) U/(α) k)^t := mul_nonneg (zero_le_one.trans (gel_pos ..))
    (pow_pos (div_pos (C.S.a_pos _) (C.S.a_pos _)) _).le
  refine ⟨x+u,by rw [map_add,hx,hu],?_⟩
  rw [← sub_sub, ← readTerminal h (hk.trans hn)]
  exact ((le_mul_of_one_le_left (size_nonneg _ _) (gel_pos ..)).trans hM).trans
    ((mul_le_mul_of_nonneg_left hL hz).trans_eq (by unfold t; ring))
end YM.OPE.Columns
