import YM.Push.CORRECTED_COLUMNS.Snap
import YM.Work.A15

/-!
# Paying each subset and recovering the Maxwell readings

On the Wilson moments and at the *raw* limiting table already; hence no
smoothness at projection ties, phase resolution, or prior rank comparison
at S needed.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Push.Corrected.Recover
open Function Set Filter MeasureTheory Lattice Wilson Cells Extraction
open scoped Topology BigOperators Matrix.Norms.Frobenius
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S T : Table C.book} {d : ℕ}
variable {X : Columns C S d} {Y : Tests X} {M : ℕ → Table C.book} {P : Prices}

section
-- Utility for pair or singleton probes. `shrink` below does not assume row limits.
private lemma subtract {n : Side} {F : Config G n → ℂ} {s : Set (Site n)} (h : Interior s F) (c : ℂ) :
    Interior s (fun x => F x-c) := by simp only [sub_eq_add_neg]; exact h.plus (Interior.constant _ _)

lemma sits (C0 : C.Makes) (Y : Tests X) (k : ℕ) : ∀ᶠ N : ℕ in atTop, ∃ h : Y.B.depth k ≤ N,
    ∀ p i c (s : Mark X i), Interior ((center C.S p ((Y.B.side_le k).trans h) 0).chamber 0) (Y.letter k N p i c s) := by
  filter_upwards [Positions.interior C0 d (Y.B.side k),eventually_ge_atTop (Y.B.depth k)] with N hn hN
  exact ⟨hN,fun p i c s => hn p _ _ (Y.B.side_le k) hN ((Y.room k i).2 _) _⟩

private lemma once {n : Side} (W : Cells.Tiling n) {F : Config G n → ℂ} {β} (h : Seam G n β) (hb : Interior (W.chamber 0) F) :
    ‖moment β F‖ ≤ W.rootTest β F := by
  have he := W.planted (ι:=Fin 1) h (fun _ => 0) (injective_of_subsingleton _) (fun _ => F) (fun _ => hb)
  simpa using he

private lemma extract_bound {A : ℕ → ℕ → ℂ} {q : ℂ} {y : ℝ}
    (ha : Tendsto (uncurry A) f.fuse (𝓝 q)) (ht : ∀ ε : ℝ, 0 < ε → f.late fun N p => ‖A N p‖ ≤ y+ε) :
    ‖q‖ ≤ y := by
  by_contra! hh
  obtain ⟨d,hp,hq⟩ := exists_between hh
  have hs : ∀ᶠ k : ℕ×ℕ in f.fuse, ‖A k.1 k.2‖ ≤ y+(d-y) := (Order.fused f _).2 (ht _ (sub_pos.mpr hp))
  have he : ‖q‖ ≤ y+(d-y) := le_of_tendsto ha.norm hs; linarith

private lemma actual_one (C0 : C.Makes) (H : Tests.Offer Y P f) (k i c j) :
    let A (N p : ℕ) := fun U : Config G (C.side N p) => Y.letter k N p i c j U - Y.one k i c j
    ∀ ε : ℝ, 0 < ε → f.late fun N p => ‖moment (C.beta N p) (A N p)‖ ≤ Real.exp (P.Q k)/ P.W k+ε := by
  intro A ε hε
  have ht := Tests.Offer.stamp Y H k ε hε
  unfold Order.late at *
  filter_upwards [ht] with a ha
  filter_upwards [ha,f.mesh.cofinal.eventually (sits C0 Y k)] with b hb hc
  obtain ⟨h,he⟩ := hb
  let N := f.mesh b; let p := f.per a; let X := center C.S p ((Y.B.side_le k).trans h) (0 : Site (C.side N p))
  have hs := he i c {j} (Finset.singleton_nonempty _)
  have hr := subtract (hc.choose_spec p i c j) (Y.one k i c j)
  refine (once X (seamless C0 _ _) (show Interior (X.chamber 0) (A N p) from hr)).trans ?_
  simp_rw [Tests.single] at hs; exact hs

private lemma actual_pair (C0 : C.Makes) (H : Tests.Offer Y P f) (k i c j l) (h : j<l) :
    let A (N p : ℕ) := fun U : Config G (C.side N p) => (Y.letter k N p i c j U-Y.one k i c j)*
      (Y.letter k N p i c l U-Y.one k i c l)-Y.pair k i c j l
    ∀ ε : ℝ, 0 < ε → f.late fun N p => ‖moment (C.beta N p) (A N p)‖ ≤ Real.exp (P.Q k)/ P.W k+ε := by
  intro A ε hε
  have ht := Tests.Offer.stamp Y H k ε hε
  unfold Order.late at *
  filter_upwards [ht] with a ha
  filter_upwards [ha,f.mesh.cofinal.eventually (sits C0 Y k)] with b hb hc
  obtain ⟨hv,he⟩ := hb
  let N := f.mesh b; let p := f.per a; let X := center C.S p ((Y.B.side_le k).trans hv) (0 : Site (C.side N p))
  have hs := he i c {j,l} (Finset.insert_nonempty ..)
  have hr s := subtract (hc.choose_spec p i c s) (Y.one k i c s)
  have hp := subtract ((hr j).times (hr l)) (Y.pair k i c j l)
  refine (once X (seamless C0 _ _) (show Interior (X.chamber 0) (A N p) from hp)).trans ?_
  simp_rw [Tests.pairs _ _ _ _ _ _ _ _ _ h] at hs; exact hs
end

variable (C0 : C.Makes) (ha : RawLimits C f T M) {t : ℕ → AxisX X → C.label d} {z : ℕ → AxisX X → ℕ → C.label d}
variable (H : Tests.Offer Y P f) (hb : Settled f Y z t)

def token (t : ℕ → AxisX X → C.label d) (k : ℕ) (i : Row X) (c : AxisX X) (s : Mark X i) : C.book.Token :=
    ⟨d,t k (Columns.Trials.names (X:=X) i c s)⟩

def only (T : Table C.book) (Y : Tests X) (t : ℕ → AxisX X → C.label d) (k : ℕ) (i : Row X) (c : AxisX X) (j : Mark X i) :=
    T.read (points fun _ : Fin 1 => Y.place k i j) fun _ => token t k i c j

def duo (T : Table C.book) (Y : Tests X) (t : ℕ → AxisX X → C.label d)
    (k : ℕ) (i : Row X) (c : AxisX X) (j l : Mark X i) :=
    T.read (points ![Y.place k i j,Y.place k i l]) ![token t k i c j,token t k i c l]
include ha hb

private lemma oneLimit (k i c j) :
    Tendsto (fun a : ℕ×ℕ => moment (C.beta a.1 a.2) (Y.letter k a.1 a.2 i c j)) f.fuse
      (𝓝 (only T Y t k i c j)) := by
  have he := returned Y ha hb k i c (fun _ : Fin 1 => j) (injective_of_subsingleton _)
  simp only [Fin.prod_univ_succ,Fin.prod_univ_zero,mul_one] at he
  refine Order.along (L:=fun N p => moment (C.beta N p) (Y.letter k N p i c j)) he
private lemma pairLimit (k i c j l) (h : j<l) :
    Tendsto (fun a : ℕ×ℕ => moment (C.beta a.1 a.2) (fun U => Y.letter k a.1 a.2 i c j U*Y.letter k a.1 a.2 i c l U)) f.fuse
      (𝓝 (duo T Y t k i c j l)) := by
  have hv : Injective ![j,l] := by
    intro a b h'
    fin_cases a <;> fin_cases b <;> simp [h.ne,h.ne'] at *
  have he := returned Y ha hb k i c ![j,l] hv
  simp only [Fin.prod_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_fin_one,Matrix.cons_val_succ,Fin.prod_univ_zero,mul_one] at he
  let A (N p : ℕ) := moment (C.beta N p) fun U => Y.letter k N p i c j U*Y.letter k N p i c l U
  have hz : (points fun x => Y.place k i (![j,l] x))=points ![Y.place k i j,Y.place k i l] := by
    ext1 x; fin_cases x <;> rfl
  have hg : (fun x : Fin 2 => token t k i c (![j,l] x))=![token t k i c j,token t k i c l] := by
    funext x; fin_cases x <;> rfl
  change Tendsto (fun a : ℕ×ℕ => A a.1 a.2) _ _
  unfold duo; rw [←hz,←hg]
  apply Order.along (L:=A) (p:=fun _ => True); exact he

include H C0
theorem single_cost (k i c j) : ‖only T Y t k i c j-Y.one k i c j‖ ≤ Real.exp (P.Q k)/P.W k := by
  apply extract_bound _ (actual_one C0 H k i c j)
  have he := oneLimit ha hb k i c j
  refine (he.sub (tendsto_const_nhds (x:=Y.one k i c j))).congr ?_
  rintro ⟨N,p⟩
  change _ = moment ..; unfold moment
  rw [integral_sub]; simp
  · exact continuous_integrable _ (show Continuous _ from C.continuousO ..)
  exact integrable_const _

omit C0 ha H hb in
private lemma unfolded {n : Side} (β : ℝ) (F H : Config G n → ℂ) (a b c : ℂ) (hf : Continuous F) (hh : Continuous H) :
    moment β (fun U => (F U-a)*(H U-b)-c)=moment β (fun U => F U*H U)-a*moment β H-b*moment β F+(a*b-c) := by
  let K U := F U*H U-a*H U-b*F U+(a*b-c)
  rw [show (fun U => (F U-a)*(H U-b)-c)=K by funext; unfold K; ring]
  unfold K moment
  have hP := continuous_integrable β (hf.mul hh)
  have hQ := continuous_integrable β (continuous_const (y:=a)|>.mul hh)
  have hW := continuous_integrable β (continuous_const (y:=b)|>.mul hf)
  let μ := law G n β
  have ha : Integrable (fun U => F U*H U-a*H U) μ := hP.sub hQ
  have hb : Integrable (fun U => F U*H U-a*H U-b*F U) μ := ha.sub hW
  change Integrable (fun U => b*F U) _ at hW
  change Integrable (fun U => a*H U) _ at hQ
  change Integrable (fun U => F U*H U) _ at hP
  change (∫ U,F U*H U-a*H U-b*F U+(a*b-c)∂μ)= _
  rw [integral_add hb (integrable_const _), integral_sub ha hW,
    integral_sub hP hQ]; dsimp only [μ]; simp only [integral_const,probReal_univ,one_smul,integral_const_mul]

theorem duo_price (k i c j l) (h : j<l) :
    let a := Y.one k i c j
    let b := Y.one k i c l
    let m := Y.pair k i c j l
    let w := Real.exp (P.Q k)/P.W k
    ‖duo T Y t k i c j l-(a*b+m)‖ ≤ w + ‖a‖*w + ‖b‖*w := by
  intro a b m w
  let o := only T Y t k i c j
  let p := only T Y t k i c l
  let r := duo T Y t k i c j l
  let g := r-a*p-b*o+(a*b-m)
  have he : ‖g‖ ≤ w := by
    apply extract_bound _ (actual_pair C0 H k i c j l h)
    refine ((((pairLimit ha hb k i c j l h).sub ((oneLimit ha hb k i c l).const_mul a)).sub
      ((oneLimit ha hb k i c j).const_mul b)).add_const (a*b-m)).congr ?_
    intro x
    exact Eq.symm (unfolded _ _ _ a b _ (C.continuousO ..) (C.continuousO ..))
  change ‖r-(a*b+m)‖≤ _
  rw [show r-(a*b+m)=g+a*(p-b)+b*(o-a) by dsimp only [g]; ring]
  refine (norm_add_le ..).trans (add_le_add ((norm_add_le ..).trans (add_le_add he ?_)) ?_)
  · rw [norm_mul]; exact mul_le_mul_of_nonneg_left (single_cost C0 ha H hb k i c l) (norm_nonneg _)
  rw [norm_mul]; exact mul_le_mul_of_nonneg_left (single_cost C0 ha H hb k i c j) (norm_nonneg _)

section
omit C0 ha H hb
private lemma unfoldOne {n} (h : n=0) (x : Points (n+1)) {G : Gauge} {L : Register G} (T : Table L) (v : Fin (n+1) → L.Token) :
    T.read x v=T.read (points fun _ : Fin 1 => x 0) fun _ => v 0 := by
  subst n; congr 1
  all_goals ext1 i; fin_cases i; rfl

private lemma unfoldTwo {n} (h : n=1) (x : Points (n+1)) {G : Gauge} {L : Register G} (T : Table L)
    (v : Fin (n+1) → L.Token) (i : Fin n) : T.read x v=T.read (points ![x 0,x i.succ]) ![v 0,v i.succ] := by
  subst n; fin_cases i; congr 1
  all_goals ext1 i; fin_cases i <;> rfl
private lemma useTwo {n} (h : n=1) (x : Points (n+1)) {G : Gauge} {L : Register G} (T : Table L)
    (v : Fin (n+1) → T.Tag) (i : Fin n) : T.useAt T x v=T.useAt T (points ![x 0,x i.succ]) ![v 0,v i.succ] := by
  subst n; fin_cases i; congr 1
  all_goals ext1 i; fin_cases i <;> rfl
end

theorem compared (hG : G.Simple) (i c) : Tendsto (fun k => T.read (Y.place k i) (token t k i c)) atTop
    (𝓝 ((X.row i).tests (standard C) X.basis (X.basis c))) := by
  let L := standard C
  let A k := T.read (Y.place k i) (token t k i c)
  let V := Retain.testFns (X:=X) i c
  let F k := L.useAt L (Y.reads k i) V
  let v := X.row i
  have hf : Tendsto F atTop (𝓝 (v.tests L X.basis (X.basis c))) := by
    have hw : Tendsto (fun k => Y.reads k i) atTop (𝓝 v.expected) := Y.B.tuned hG v.expected
    have hp := generic_conf _ v.probes
    have hx := ((L.class_smooth L (Maxwell.table_smooth _) V).continuousOn.continuousAt ((conf_open _).mem_nhds hp)).tendsto.comp hw
    have hu : V= Fin.cons (α:=fun _ => L.Tag) ⟨d,X.basis c⟩ (fun j => ⟨d,X.basis (v.uses j)⟩) := by
      ext1 j; refine Fin.cases ?_ (fun j => ?_) j <;> rfl
    exact show Tendsto F atTop (𝓝 _) from by
      apply (show L.useAt L v.expected V=v.tests L X.basis (X.basis c) by rw [hu]; rfl) ▸ hx
  suffices he : Tendsto (fun k => A k-F k) atTop (𝓝 0) by
    have hh := he.add hf; simp only [zero_add,sub_add_cancel] at hh; exact hh
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  rcases eq_or_ne v.extra 0 with h|h
  · apply squeeze_zero (fun _ => norm_nonneg _) _ P.runs
    intro k
    have hp : A k=only T Y t k i c 0 := by unfold A; exact unfoldOne h _ _ _
    have hq : F k=Y.one k i c 0 := by
      exact unfoldOne h _ L (fun j => Ward.expose (V j))
    change ‖A k-F k‖ ≤ _; rw [hp,hq]; exact single_cost C0 ha H hb k i c 0
  have he : v.extra=1 := by have := v.cap; omega
  let a : Fin v.extra := ⟨0,by omega⟩
  let b := a.succ
  let f (x : Mark X i) k := ‖Y.one k i c x‖
  have hg x : ∃ A : ℝ,Tendsto (f x) atTop (𝓝 A) := by
    let Z (y : Points (v.extra+1)) := points fun _ : Fin 1 => y x
    let w : Fin 1 → L.Tag := fun _ => ⟨d,label X i c x⟩
    have hx : Z v.expected∈conf _ := injective_of_subsingleton _
    have hz : Continuous Z := by unfold Z points; fun_prop
    refine ⟨‖L.useAt L (Z v.expected) w‖,?_⟩
    exact (((L.class_smooth L (Maxwell.table_smooth _) w).continuousOn.continuousAt ((conf_open _).mem_nhds hx)).tendsto.comp
      (hz.continuousAt.tendsto.comp (Y.B.tuned hG v.expected))).norm
  let w k := Real.exp (P.Q k)/P.W k
  obtain ⟨M0,H0⟩ := hg 0; obtain ⟨Mb,Hb⟩ := hg b
  have hv : Tendsto (fun k => w k+f 0 k*w k+f b k*w k) atTop (𝓝 0) := by
    simpa only [mul_zero,add_zero] using (P.runs.add (H0.mul P.runs)).add (Hb.mul P.runs)
  refine squeeze_zero (fun _ => norm_nonneg _) (?_) hv
  intro k
  have hp : A k=duo T Y t k i c 0 b := unfoldTwo he _ _ _ a
  have hq : F k=Y.one k i c 0 * Y.one k i c b +Y.pair k i c 0 b := by
    rw [Tests.pair,add_sub_cancel]
    exact useTwo he _ L V a
  change ‖A k-F k‖ ≤ _; rw [hp,hq]; exact duo_price C0 ha H hb k i c 0 b (by exact Fin.succ_pos a)
end YM.Push.Corrected.Recover
