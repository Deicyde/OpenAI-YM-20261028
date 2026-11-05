import YM.Next.RANK.SealMix

/-!
# Tilt regular bulk on arrays

At the initial k stop move all H to threshold q. Permit arbitrary nonempty
marker firings. No rewriting of previous K until paying for every failed mask.
For restraining later pure outputs on larger masks, reuse refusal form.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Edition
open Function Filter RG Thirst Lattice Wilson MeasureTheory Relation Corona Value Glyph Marker Perch Vac.Numbers Alarm Spindle Station Cells Atlas Finset Baler Source EntryWord
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius

variable {G : Gauge} {n : Side} {A : Activities G n} {Q : Rep G n} {V ι κ : Type} [Fintype V] [DecidableEq V]
variable {d : ℕ} {ζ : V→ Site n} {t τ : ℝ} {p q : BudgetPoint} {e u v : ℝ}

-- H append
lemma Unpacks.relax {X : ι→SourceAt G ζ} {r} {a b : ℝ} (h : Unpacks X p r e a) (hb : a ≤ b) : Unpacks X p r e b:= by
  obtain ⟨x,H,h⟩:=h; exact ⟨x,H,fun i=> ⟨(h i).1,(h i).2.1,(h i).2.2.trans hb⟩⟩
lemma stars_add [Fintype ι] [Fintype κ] {X : ι→modes V} {P : ι→Support n} {Y : κ→modes V} {Q : κ→Support n}
    {a b:ℝ} {f : ι→ℝ} {g : κ→ℝ} (hf : ∀ i,0≤f i) (hg : ∀ i,0≤g i) (Hx : stars p X P e f a) (Hy : stars p Y Q e g b) :
    stars p (Sum.elim X Y) (Sum.elim P Q) e (Sum.elim f g) (a+b):= by
  intro x; apply (sum_pay ..).2
  · rw [Fintype.sum_sum_type]; apply add_le_add
    · simpa only [pay,Sum.elim_inl,tsum_fintype] using! (Hx x).2.2
    simpa only [pay,Sum.elim_inr,tsum_fintype] using! (Hy x).2.2
  intro i; apply mul_nonneg _ (Real.exp_pos _).le; rcases i with i|i; exacts [hf _,hg _]
lemma Unpacks.mix [Fintype ι] [Fintype κ] {X : ι→SourceAt G ζ} {Y : κ→SourceAt G ζ} {a b : ℝ} {r} (h : Unpacks X p r e a) (hp : Unpacks Y p r e b):
    Unpacks (Sum.elim X Y) p r e (a+b) := by
  obtain ⟨m,hm,hx⟩:=h; obtain ⟨L,hL,hs⟩:=hp
  refine ⟨Sum.elim m L,fun i=> ?_,?_⟩
  · rcases i with i|i; exacts [hm _,hL _]
  convert stars_add (fun i=> (hm i).1) (fun i=> (hL i).1) hx hs using 1 <;> (ext1 i; cases i <;> rfl)
lemma Credit.relax {H : ι→SourceAt G ζ} {r a} (h : Credit H p q r e a) {f : ℝ} (hf:a≤f) : Credit H p q r e f:= by
  obtain ⟨x,h,hp⟩:=h; exact ⟨x,h,fun i=>⟨(hp i).1,(hp i).2.1,(hp i).2.2.trans hf⟩⟩
lemma Credit.mix [Fintype ι] [Fintype κ] {H : ι→SourceAt G ζ} {X : κ→SourceAt G ζ} {r a b} (h : Credit H p q r e a) (hp : Credit X p q r e b) :
    Credit (Sum.elim H X) p q r e (a+b):= by
  obtain ⟨m,hm,hM⟩:=h; obtain ⟨f,H,hF⟩:=hp
  refine ⟨Sum.elim m f,fun i=>?_,?_⟩
  · rcases i with i|i; exacts [hm _,H _]
  convert stars_add (fun i=> (hm i).1) (fun i=> (H i).1) hM hF using 1 <;> (ext1 i; cases i<;>rfl)

lemma Credit.spill {H : ι→ SourceAt G ζ} {a e' : ℝ} (v : V→ℝ) (h : Credit H p q v e a) (hb : q.threshold≤p.threshold)
    (hp : e'≤ e) (hz : 0 ≤e') : Unpacks H q v e' a:= by
  obtain ⟨f,hm,hx⟩:=h
  refine ⟨f,fun i=> (transferD ..).2 ⟨hm i|>.1,fun U hu=> ((transferD ..).1 (hm i)).2 _ (threshold_fit _ _ hb _ hu)⟩,fun i=> ?_⟩
  have H':= hx i; let P:=pay (fun i=>f i *debt q.B e' (H i).extent) (fun j=>i∈ (H j).fires.val)
  let Q:=pay (fun i=>f i *debt q.B e (halo 8 (H i).extent)) (fun j=>i∈ (H j).fires.val)
  change SumBudget Q a at H'; change SumBudget P a
  have hP j:0≤P j:= by unfold P pay;split; exact mul_nonneg (hm _|>.1) (Real.exp_pos _).le;exact le_rfl
  have hQ j: P j≤Q j:= by
    unfold P Q pay;split;swap; exact le_rfl
    refine mul_le_mul_of_nonneg_left ((debt_mono _ hp _).trans <| Real.exp_le_exp.mpr <| mul_le_mul_of_nonneg_left ?_ (le_trans hz hp)) (hm j|>.1)
    exact_mod_cast cover_mono (halo_subset ..) q.B
  have hv:=H'.2.1.of_nonneg_of_le hP hQ; exact ⟨hP,hv,(hv.tsum_le_tsum hQ H'.2.1).trans H'.2.2⟩

lemma send_plus (t : Glyph.modes V) (c d : ℂ) : Poly.send t (c+d)=Poly.send t c+Poly.send t d:= by
  ext i; rw [Poly.part_plus]; simp only [Poly.part_send];split_ifs<;>simp
lemma send_zero (t : modes V) (x : ℂ) (h : t.val.Nonempty): (Poly.send t x).part (quiet V)=0:= by
  simp only [Poly.part_send];exact if_neg fun h' => h.ne_empty (Subtype.ext_iff.mp h'.symm)
lemma solo_pass (t : modes V) (x : ℂ) (h : t.val.Nonempty) : Poly.pass (Poly.send t x)=Poly.send t x+1:= by
  let W:= Poly.send t x; let a:=Fintype.card V
  have ht : W.part (quiet _)=0 := send_zero t x h
  have hP : W^2=0:= by unfold W; rw [sq,plate_pair]; exact if_neg fun H=> Finset.disjoint_left.mp H h.choose_spec h.choose_spec
  change Poly.pass W=W+1
  rw [Exponential.pass_extend ht (a+1) (by dsimp [a]; omega),sum_range_succ',sum_range_succ']
  have he (i : ℕ) : W^(i+1+1)=0 := by rw [show i+1+1=i+2 from rfl,pow_add,hP,mul_zero]
  simp_rw [he]; simp [W]

variable (p q)

def dash (X : SourceAt G ζ) (h : q.threshold≤p.threshold) : Strike G ζ q.threshold where
  extent:=halo 8 X.extent
  fires:=X.fires
  active:= by obtain ⟨a,ha⟩:=X.chosen; exact ⟨ζ a, halo_subset _ _ (X.remembers a ha)⟩
  remembers i hi:=halo_subset _ _ (X.remembers i hi)
  value U:= masked p.threshold X.extent X.value U-masked q.threshold X.extent X.value U
  meas:= (masked_measurable _ _ _ X.meas).sub (masked_measurable _ _ _ X.meas)
  inv k U:= congr_arg₂ (·-·) (sails _ _ _ X.inv k U) (sails _ _ _ X.inv k U)
  sees U V a _:= congr_arg₂ (·-·) (sail _ _ _ X.loc U V a) (sail _ _ _ X.loc U V a)
  only U hU:=awake_mask X.extent _ h U hU

lemma dash_amount (X : SourceAt G ζ) (h : q.threshold≤p.threshold) (U) : X.amount p.threshold U=X.amount q.threshold U+(dash p q X h).occ U:= by
  unfold SourceAt.amount Strike.occ dash; dsimp only; rw [← send_plus,add_comm,sub_add_cancel]
lemma dash_paid (H : SourceAt G ζ) (h : q.threshold≤p.threshold) (r : V→ℝ) {a : ℝ} (hp : transported H p.threshold r a) : Taxed (dash p q H h) (q:=q) r a := by
  refine ⟨hp.1,fun U=>?_⟩
  dsimp only [dash]; by_cases he:Healthy q.threshold H.extent U
  · rw [masked_eq _ _ _ _ he,masked_eq _ _ _ _ (threshold_fit _ _ h _ he),sub_self,norm_zero,mul_zero]; exact hp.1
  rw [masked_ne _ _ _ _ he,sub_zero]; by_cases hb:Healthy p.threshold H.extent U
  · rw [masked_eq _ _ _ _ hb]; exact ((transferD ..).1 hp).2 U hb
  rw [masked_ne _ _ _ _ hb,norm_zero,mul_zero]; exact hp.1
lemma dash_credit {H : ι→SourceAt G ζ} {r} (h : Credit H p q r (e+1) u) (ht : q.threshold≤ p.threshold) (hr : Injective ζ) (he : 0 ≤ u):
    taxable (fun i=> dash p q (H i) ht) r e (wilt q.B*u):= by
  obtain ⟨f,hf,h⟩:=h
  exact ⟨f,fun i=> dash_paid p q (H i) ht _ (hf i), roots_hits _ _ _ hr (fun i=>(H i).chosen) (fun i j hj=> halo_subset _ _ ((H i).remembers j hj)) (fun i=> (hf i).1) he h⟩

variable {p q}

lemma taxable.add [Fintype ι] [Fintype κ] {B : ι→Strike G ζ p.threshold} {Y : κ→ Strike G ζ p.threshold} {r e a b}
    (h : taxable (q:=p) B r e a) (hp : taxable (q:=p) Y r e b): taxable (q:=p) (Sum.elim B Y) r e (a+b):= by
  obtain ⟨Q,hQ,hρ⟩:=h; obtain ⟨u,hu,hU⟩:=hp;let C:=Sum.elim Q u; let S:=Sum.elim B Y
  have ht x : Taxed (S x) (q:=p) r (C x):= by rcases x with x|x; exacts [hQ _,hu _]
  refine ⟨C,ht,fun i=>?_⟩; apply (sum_pay ..).2
  · rw [Fintype.sum_sum_type]; apply add_le_add
    · simpa only [tsum_fintype,C,S,Sum.elim_inl,pay] using! (hρ i|>.2.2)
    simpa only [tsum_fintype,C,S,Sum.elim_inr,pay] using! (hU i|>.2.2)
  intro i; exact mul_nonneg (ht i|>.1) (Real.exp_pos _).le
lemma taxable.relax {X : ι→Strike G ζ q.threshold} {a b r e} (h : taxable (q:=q) X r e a) (hb : a≤b): taxable (q:=q) X r e b:=by obtain ⟨m,hm,hx⟩:=h; exact ⟨m,hm,fun i=>⟨(hx i).1,(hx i).2.1,(hx i).2.2.trans hb⟩⟩
lemma Burden.up {X : ι→Lifted G ζ t} (q : BudgetPoint) {a b r e} (h : Burden X q r e a) (hb:a≤b): Burden X q r e b:=by obtain ⟨m,hm,hx⟩:=h; exact ⟨m,hm,fun i=>⟨(hx i).1,(hx i).2.1,(hx i).2.2.trans hb⟩⟩
end YM.Next.Rank.Edition
