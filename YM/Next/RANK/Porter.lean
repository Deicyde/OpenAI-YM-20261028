import YM.Next.RANK.Anglo
import YM.Next.RANK.Vents

/-!
# Distribute from orientation and sum

Keep exponents before normalization across site. Reserve precisely. -/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Alarm
open Function Filter RG Thirst Baler Lattice Wilson Finset MeasureTheory Relation Corona Value Glyph Marker PathData
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius

variable {G : Gauge} {n : Side} {p q : BudgetPoint} {r : ℕ} {ι χ : Type}
variable {C : Clip} {t τ μ E c : ℝ}

/-- Anchored total panel to be copied to all affine channels. -/
structure Dial (W : ι→Wickless G n t) (q : BudgetPoint) (e w : ℝ):Prop where
  place i : 0∈(W i).extent
  toll : ∃ b : ι→ℝ,(∀ i,0≤b i ∧ ∀ U,|(W i).value U| ≤ b i) ∧ SumBudget (fun i=> b i*debt q.B e (W i).extent) w



def scaleTerm (w : ℝ) (B : Wickless G n t) : Wickless G n t where
  extent := B.extent
  active := B.active
  value U:= w* B.value U
  inv i U:= congr_arg (w*·) (B.inv i U)
  meas:= measurable_const.mul B.meas
  sees U V a b:= congr_arg (w*·) (B.sees U V a b)
  untouched U h:=by rw [B.untouched U h,mul_zero]

abbrev panelV (ι : Type) (n : Side) := Signed × Site n × ι
variable (W : ι→Wickless G n t)

-- all r rotations on payload evaluated at true origin

def turnP (B : Wickless G n t) (s : Signed) (x : Site n) : Wickless G n t where
  extent:= swath s x B.extent
  active:= B.active.image _
  value:= B.value∘pull s x
  inv:= p_invar _ _ B.inv
  meas:= B.meas.comp (continuous_pull ..|>.measurable)
  sees:= final_swath s x B.extent t B.sees
  untouched _ h:=B.untouched _ ((s_healthy s x ..).2 h)

def family (w : ℝ) (i : panelV ι n) := scaleTerm w (turnP (W i.2.2) i.1 i.2.1)

lemma orbiting (w : ℝ) : Garden (family W w) := by
  intro s x
  let G':= (Equiv.prodCongr (Equiv.mulLeft s) (Equiv.prodCongr (sends s x) (Equiv.refl ι)))
  refine ⟨G',fun i=> ?_⟩; constructor
  · exact (swath_comp s x i.1 i.2.1 _).symm
  intro U; apply congr_arg (w*·); exact (congr_arg (W i.2.2 |>.value) (pull_pull ..)).symm

lemma slice_total {Y : Type*} [Fintype Y] (j : Y → ι→ℝ) (hj : ∀ i,Summable (j i)) :
    Summable (fun i:Y×ι=>j i.1 i.2) ∧ ∑' i:Y×ι,j i.1 i.2=∑ k,∑' i,j k i := by
  let f:=fun i : Y×ι=> j i.1 i.2
  have h : Summable f := Summable.of_norm ((summable_prod_of_nonneg (f:=fun i => ‖f i‖) (fun i=>norm_nonneg _)).mpr ⟨fun i=> (hj i).abs,(hasSum_fintype _).summable⟩)
  exact ⟨h,h.tsum_prod.trans (tsum_fintype ..)⟩

-- cost from shape

lemma rioting {p : BudgetPoint} {w : ℝ} (h : Dial W p (E+1) μ) : Verse (family W w) p E (wilt p.B * (Fintype.card Signed* (|w| *μ))) := by
  obtain ⟨c,hc,hC⟩:=h.toll
  let X := family W w; let Z:=fun i=>(X i).extent
  let P i:panelV ι n := i
  let f:=fun i : panelV ι n=> |w| *c i.2.2
  have he (s : panelV ι n) : 0≤f s:=mul_nonneg (abs_nonneg _) (hc _).1
  have hh i: i.2.1∈Z i := by
    unfold Z X; dsimp only [family,turnP,scaleTerm];simpa [affine] using! (stay i.1 i.2.1 _|>.2 (h.place _))
  refine ⟨f,fun i=> ⟨he _,fun U=>?_⟩,circle (n:=n) Z _ _ hh _ f p.B_pos he _ ?_⟩
  · dsimp only [family,turnP,scaleTerm,Function.comp_apply]; rw [abs_mul]; exact mul_le_mul_of_nonneg_left ((hc _).2 _) (abs_nonneg _)
  let d i:=c i*debt p.B (E+1) (W i|>.extent)
  intro y; let T:= pay (fun i => f i*debt p.B (E+1) (Z i)) (fun i=> i.2.1=y)
  have ht i:0≤T i:=by unfold T pay; split_ifs; exact mul_nonneg (he _) (Real.exp_pos _).le; exact le_rfl
  have hv i j k:T (i,j,k)= if j=y then |w| *d k else 0 := by
    dsimp only [T,Z,X,f,d,debt,pay,family,turnP,scaleTerm]; rw [swath_cover]; split_ifs; exact mul_assoc ..; rfl
  have hx (i : Signed) (x:Site n) : Summable fun j=> T (i,x,j):= by
    simp_rw [hv]; by_cases he:x=y<;>simp only [he,↓reduceIte]; exact hC.2.1.mul_left _; exact summable_zero
  have hy (i : Signed) := slice_total (fun x : Site n=>fun j=> T (i,x,j)) (hx i)
  have hM:= slice_total (fun i : Signed=>fun j=>T (i,j)) (fun i => (hy i).1)
  refine ⟨ht,hM.1,hM.2.le.trans ?_⟩
  have hX (i) : ∑' j,T (i,j) = |w| *(∑' j, d j) := by
    refine (hy i).2.trans ?_; rw [sum_eq_single y]
    · simp only [hv,↓reduceIte]; rw [tsum_mul_left]
    · intro j _ hj; simp only [hv,if_neg hj,tsum_zero]
    simp
  simp_rw [hX (i:=_)]
  simp only [sum_const,card_univ,nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hC.2.2 (abs_nonneg _)) (Nat.cast_nonneg _)

lemma blossom [Countable ι] {W : ι→Wickless G n q.threshold} (h : Dial W q (E+1) c) (he : 0≤E)
    (U : Config G n→ℝ) (hp : ∀ V,U V=∑' i,(W i).value V) (w : ℝ) : Volunteer (fun x=> w*rag U x) q E (wilt q.B*(|w| *c)) := by
  let z:ℝ:= (Fintype.card Signed:ℝ)
  have hz : 0 < z:= Nat.cast_pos.mpr Fintype.card_pos
  let P:= family W (w*z⁻¹)
  have hh : Verse P q E (wilt q.B*(|w| *c)) := by
    rw [show |w| *c=z*(|w*z⁻¹| *c) by rw [abs_mul,abs_of_nonneg (inv_pos.mpr hz).le]; field_simp];exact rioting W h
  refine ⟨panelV ι n,inferInstance,P,orbiting W _,hh,fun x=>?_⟩
  let H i:=(P i).value x
  have he : Summable H:= summable_verse hh he x
  have hv (i : Signed) : (∑' v,H (i,v))=∑ y : Site n,(w*z⁻¹)*U (pull i y x) := by
    have hs (a : Site n) : Summable fun j=> H (i,a,j):=  (he.prod_factor i).prod_factor a
    apply (slice_total (fun (a:Site n) (b:ι)=>H (i,a,b)) hs).2.trans; apply sum_congr rfl; intro i _; rw [hp]
    unfold H P; simp only [family,scaleTerm,turnP,Function.comp_apply]; rw [tsum_mul_left]
  change _= ∑' i,H i; symm; rw [he.tsum_prod,tsum_fintype]; unfold rag; simp_rw [hv, ←mul_sum]; dsimp only [z]; ring
end YM.Next.Rank.Alarm
