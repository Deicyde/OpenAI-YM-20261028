import YM.RG08.Tall.Heard
import YM.RG08.Scale.Mate
/-!
# Reexpressing *local* germ-normalized source in powers of coarse coupling

One formula compatible with changing also to ratios referenced anywhere on the window. Not
statement about actual physical coupling.
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
noncomputable section
namespace YM.RG08.Tall
open Function Filter Lattice Wilson Exterior Bloch Next.Free Work.F08 RG Laurent Precision Finset
open Quire Stationary Scores Scores.Pages Matrix Push.AbsoluteSums PertExtension.Chart PertExtension.Series PertExtension.Series.Radial PertExtension.Series.Tested Shade Reflect Analysis Loom MeasureTheory Conductor PowerSeries
open scoped Topology ContDiff Classical BigOperators
variable {I α E : Type} {G : Gauge} {D p n r k τ ε j h Λ l L : ℕ} {m c f : Side} {R : ℝ} {i : Site m}

variable (X : PowerSeries ℝ) (hX : constantCoeff X=1)
-- k incoming grade U pre; valuation shift can be zero or even (actual branch),
-- allow general comparison. X normalized ratio old coupling / new.
def glaze (r k u : ℕ) : ℝ := coeff u (X^k * (X⁻¹)^r)
include hX in
lemma glaze_zero (r k : ℕ): glaze X r k 0=1 := by simp [glaze,coeff_zero_eq_constantCoeff_apply,hX]
include hX in
lemma glaze_refer (he:τ + k=r+j)(n) : glaze X r k n=glaze X τ j n := by
  apply congr_arg (coeff n); let W: PowerSeries ℝ:= X⁻¹
  have hg:∀ i:ℕ,W^i*X^i=1:=fun i=> by rw [←mul_pow,show W*X=1 from PowerSeries.inv_mul_cancel _ (hX ▸ one_ne_zero),one_pow]
  calc
    X^k * W^r = X^(k+τ)*(W^r * W^τ) := by rw [pow_add]; nth_rw 1 [← one_mul (X^k)]; rw [←hg τ]; ring
    _ = X^j * W^τ := by rw [show k+τ=r+j by omega,pow_add]; calc _=(X^j*W^τ)*(W^r*X^r) := by ring
                                                                  _=_:=by rw [hg,mul_one]
-- This is the actual substitution, including coordinate `new/old` on each displayed leg.
lemma glaze_orient (P : Reel ℝ) (r k) :
    coeff k ((X⁻¹)^r* PowerSeries.subst (PowerSeries.X*X) (mk P))=∑ j∈range (k+1),glaze X r j (k-j)* P j := by
  let V:= fun i=> coeff i X; have he:X=mk V:=by ext i; rw [coeff_mk]
  let e:= ∑ j∈range (k+1), C (P j)*(PowerSeries.X*X)^j
  have hb (i)(hp:i≤k) : coeff i (PowerSeries.subst (PowerSeries.X*X) (mk P))=coeff i e := by
    unfold e; rw [he, show PowerSeries.X*mk V=Span V from rfl,merge_f,map_sum]; simp_rw [coeff_C_mul, Span,mul_pow,coeff_X_pow_mul']
    calc
      _=∑ j∈range (i+1), P j*(if j ≤ i then coeff (i-j) (mk V ^ j) else 0):=sum_congr rfl fun j hj=> by rw [if_pos (show j ≤ i from by have ht:=mem_range.mp hj; omega)]; rfl
      _=_:=sum_subset (range_mono (Nat.succ_le_succ hp)) (fun j hj h=> by rw [if_neg (by simp only [mem_range] at h; omega),mul_zero])
  have h : coeff k ((X⁻¹)^r*PowerSeries.subst (PowerSeries.X*X) (mk P))=coeff k ((X⁻¹)^r*e):= by rw [coeff_mul,coeff_mul]; exact sum_congr rfl fun i hi=>by rw [hb _ (by have h:=mem_antidiagonal.mp hi; omega)]
  rw [h]; unfold e; rw [Finset.mul_sum,map_sum]; apply sum_congr rfl; intro j hj; rw [mul_pow,show (X⁻¹)^r*(C (P j)*(PowerSeries.X^j*X^j))= C (P j)*(PowerSeries.X^j*(X^j*(X⁻¹)^r)) by ring,coeff_C_mul,coeff_X_pow_mul',if_pos (Nat.le_of_lt_succ (mem_range.mp hj))]; exact mul_comm ..

variable [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
def hill (F : Screed E α) (e r : ℕ) := ∑ i∈ range (e+1), glaze X r i (e-i) • F i r
lemma hill_rank {F : Screed E α}(h : Fits τ F)(he : ∀ i r,Tidy (F i r)) : Fits τ (hill X F) ∧ ∀ i r,Tidy (hill X F i r) := by
  constructor
  · intro e r hr; contrapose! hr
    refine sum_eq_zero fun i hi=>?_ ; rw [not_ne_iff.mp (mt (h i r) (by have h:=mem_range.mp hi; omega)),smul_zero]
  exact fun i r=> Tidy.additions fun j _=> (he j r).scale _
lemma hill_add (F H:Screed E α) : hill X (F+H)=hill X F+hill X H := by ext1 i; ext1 j; simp only [hill,Pi.add_apply,smul_add,sum_add_distrib]
lemma hill_sub (F H:Screed E α) : hill X (F-H)=hill X F-hill X H := by funext i j; simp only [hill,Pi.sub_apply,smul_sub,sum_sub_distrib]
lemma hill_weight (F:Screed E α)(t:ℝ) : hill X (t • F)=t • hill X F := by funext i j; simp only [hill,Pi.smul_apply,Finset.smul_sum,smul_comm t]
include hX in
lemma ridge (e r : ℕ)(F : Screed E α) : hill X F e r=F e r+∑ i∈range e,glaze X r i (e-i) • F i r := by rw [hill,Finset.sum_range_succ, tsub_self,glaze_zero X hX,one_smul]; exact add_comm ..
lemma summons {F:Screed E α}(v : E→L[ℝ] ℝ) (k j : ℕ) : v ∘ hill X F k j=hill X (fun i j=> v ∘ F i j) k j := by funext p; simp [hill, Function.comp_apply, Finset.sum_apply]
variable {U V:BoardU D R G}
include hX
lemma tune_grade {U:Screed ℝ (Loc G 1)} (τ q : ℕ)(h : Fits τ U) :
    Loom.strand τ q (hill X U)= fun r=> ∑ i∈range (q+1), glaze X τ i (q-i) • Loom.strand τ i U r := by
  ext1 r; unfold Loom.strand
  split
  next hp=>
    let u:=q+r-τ; let L:Finset ℕ:= (range (u+1)).filter fun j=> r≤τ+j; let K:Finset ℕ:= (range (q+1)).filter fun j=>τ≤ j+r
    let F i:= glaze X r i (u-i) • U i r; let G i:=glaze X τ i (q-i) • (if τ ≤ i+r then U (i+r-τ) r else 0)
    change ∑ j∈range (u+1),F j=∑ j∈range (q+1),G j
    rw [← sum_subset (s₁:=L) (f:=F) (filter_subset ..) ?_,←sum_subset (s₁:=K) (f:=G) (filter_subset ..) ?_]; rotate_left
    · intro i hi hg; unfold G; rw [if_neg (fun hv=>hg (mem_filter.mpr ⟨hi,hv⟩)),smul_zero]
    · intro i hi hg; unfold F; rw [not_ne_iff.mp (mt (h i r) (fun hv=> hg (mem_filter.mpr ⟨hi,hv⟩))),smul_zero]
    apply sum_nbij' (fun i=>τ+i-r) (fun i=>r+i-τ)
    · intro i hi; simp only [mem_filter,mem_range,L,K,u] at hi ⊢; omega
    · intro i hi; simp only [mem_filter,mem_range,L,K,u] at hi ⊢; omega
    · intro i hi; change _-_ = _; change i∈L at hi; simp only [mem_filter,mem_range,L,u] at hi; omega
    · intro i hi; change _-_ = _; change i∈K at hi; simp only [mem_filter,mem_range,K,u] at hi; omega
    intro i hi; unfold F G; simp only [mem_filter,mem_range,L,u] at hi; unfold u; rw [if_pos (by omega),show τ+i-r+r-τ=i by omega]; congr 1; rw [glaze_refer X hX (show τ+i=r+(τ+i-r) by omega)]; congr 1; omega
  next hp=>symm; refine sum_eq_zero fun i hi=>?_ ; rw [if_neg ?_,smul_zero]; have hh:=mem_range.mp hi; omega

-- assembling Cargo across *finite* weighted sums of different q.
theorem ridges (h : Marvel τ U): Marvel τ (hill X U) := by
  refine ⟨(hill_rank X h.cap h.hem).1,(hill_rank X h.cap h.hem).2,fun m φ i=>?_⟩
  let F j r:= plug φ R ∘ U j r
  rw [show (fun j r=> plug φ R∘hill X U j r)=hill X F from funext fun k=> funext fun r=>summons X ..]
  refine vocalized (fun p=> ?_); have hh : ∀ i j,Tidy (F i j) := fun i j=> Tidy.map _ (h.hem i j)
  obtain ⟨q,hq⟩:= Shore.vessel (h.wardrobe m φ i) hh p
  let a (j:ℕ) (k : ℕ):= glaze X τ k (j-k) • q k
  let v (j:ℕ):=∑ k∈range (j+1),a j k
  have hz j : Shell G m (v j) := by
    suffices ∀ s : Finset ℕ,Shell G m (∑ k∈s, a j k) from this _
    intro s; induction s using Finset.induction_on with
    | empty=> rw [sum_empty]; exact shell_zero
    | insert k s hs ih=> rw [sum_insert hs]; exact Shell.plus (Shell.scale (hq k).toShell _) ih
  refine ⟨v,fun k=> ⟨hz k,fun j hj=>?_⟩⟩
  rw [tune_grade X hX τ k (Fits.echo h.cap φ)]; unfold v; dsimp only
  rw [show (∑ k'∈_,a k k') ∘ input G m=(∑ z∈range (k+1), a k z∘input G m) from funext fun m=>by simp [Function.comp_apply,Finset.sum_apply]]
  rw [Tensor.coeff_sum, st_sums]; rotate_left
  · intro z _; exact (((strand_tid (k:=z) hh).pens.scale _)).of_norm
  · intro z _; exact (((hq z).hol.of_le le_top).const_smul (glaze X τ z (k-z)))
  refine sum_congr rfl fun z _=>?_ ; rw [st_scale _ ((strand_tid hh).pens.of_norm),← (hq z).scores_at j hj]
  exact Tensor.coeff_smul _ ((hq z).hol.of_le le_top)
omit hX in
lemma rink (hp : Marvel τ U) (hq : Marvel τ V) {s : Signed} (h : Honor s U V m) : Honor s (hill X U) (hill X V) m := by
  intro i φ e r v
  let B (Y:BoardU D R G) (g : Exam D)(k:ℕ):= plug g R∘Y k r
  let P (k:ℕ):= glaze X r k (e-k) • B U φ k
  let Q (k:ℕ):= glaze X r k (e-k) • B V (twisting s φ) k
  have hz : ∀ k,Pens (B U φ k) := fun k=> (hp.hem k r).pens.shaped _
  have he : ∀ k,Pens (B V (twisting s φ) k) := fun k=>(hq.hem k r).pens.shaped _
  dsimp only; rw [summons,summons]
  rw [hill,hill]; change rootSong (∑ k∈range _,P k) m _ _=rootSong (∑ k∈range _,Q k) m _ _
  rw [root_sum _ _ P (fun k _=>(hz k).scale _),Finset.sum_apply,root_sum _ _ Q (fun k _=>(he k).scale _),Finset.sum_apply]; exact sum_congr rfl (fun b _=> by unfold P Q; rw [root_scale _ (hz b),root_scale _ (he b)]; exact congr_arg (glaze X r b (e-b) • ·) (h _ φ b r v)) -- wrong b
-- adapter scalar cues to hX step story
end YM.RG08.Tall
