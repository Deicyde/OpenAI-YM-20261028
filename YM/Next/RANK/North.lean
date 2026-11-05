import YM.Next.RANK.Respire
import YM.Next.RANK.Rifle
import YM.Next.RANK.River
import YM.Next.RANK.Screen
import YM.Next.RANK.Spaces
import YM.Shift.Osc

/-!
# Long H at k

E root threshold conversion of all non-anchors first; read on OLD masks all
fields incl non-global healthy; beliefs in unmasked values off masks do not
need budgets.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Edition
open Function Filter RG Thirst Lattice Wilson MeasureTheory Relation Corona Value Glyph Marker Perch Vac.Numbers Alarm Spindle Station Cells Atlas Finset Baler Source Labels
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius ContDiff

variable {G : Gauge} {n : Side} {C : Family G} {N k d i p : ℕ}
variable {V : Type} [Fintype V] [DecidableEq V]

lemma pack_complex {ι β : Type} [Fintype β] [DecidableEq β] (f : ι→ℂ) (x : ι→β) (h : Summable f) :
    (∑ i:β, ∑' j,(if x j=i then f j else 0))=∑' j,f j:= by
  have he (i : β): Summable fun j=> if x j=i then f j else 0:= (h.indicator (s:={j|x j=i})).congr (by intro j;by_cases h:x j=i<;>simp [Set.indicator,h])
  rw [← Summable.tsum_finsetSum (fun i _=> he i)]; apply tsum_congr; intro i; simp

lemma pr_dot (s : Signed) (x : Site n) (a : Prop) (U : Config G n) (P : Support n) (t : ℝ) (F : Config G n→ℂ) :
    dot a (masked t P F (pull s x U))= masked t (swath s x P) (dot a∘F∘pull s x) U:= by
  by_cases h : Healthy t P (pull s x U)
  · rw [masked_eq _ _ _ _ h,masked_eq _ _ _ _ ((s_healthy s x ..).1 h)];rfl
  rw [masked_ne _ _ _ _ h,masked_ne _ _ _ _ (mt (s_healthy s x t U P).2 h),dot_zero]

abbrev Keepat (n : Side):={ A : Support n // 0∈ A }

def fulcrum {ζ : V→Site n} (i : V) {X : Support n} (h : ζ i∈X) (F : Config G n→ℂ) {b} (he : Reliable b G n X F): SourceAt G ζ where
  extent:=X
  fires:=slot i
  chosen:=singleton_nonempty _
  remembers _ hh:=(mem_singleton.mp hh).symm▸ h
  value:=F
  meas:=he.meas
  loc:=he.locally
  inv:=he.inv

variable (v : C.label d) (i k N p)
def boxat (X : Keepat (C.side k p)) (U : Config G (C.side k p)) := ∑' j, if (wideX C v i k N p j) = X.val then
      wideW C v i k N p j*wideA C v i k N p j U else 0
variable {i k N p}
lemma freeat (h : C.Makes) (hk : C.ref d≤k) (hN : k≤N) (i) {s : ℝ} (X) : Reliable s G _ X.val (boxat N k i p v X):= by
  have ht:= (receipts C i h hk hN v p).2
  obtain ⟨z,h,-⟩:=ht.pays
  refine ⟨fun j U=> tsum_congr fun t=>?_ ,Measurable.tsum ?_,fun U V H=> ?_⟩
  · rw [(h t).1.symmetry ..]
  · intro j; split; exact measurable_const.mul (h j|>.1.borel); exact measurable_const
  apply tsum_congr;intro j;split
  · rename_i h'; rw [(h j).1.sites _ _ (h'.symm ▸ H)]
  rfl

section
variable (h : C.Makes) (hk : C.ref d≤k) (hN : k≤N)
variable {ζ : V→Site (C.side k p)} (x : V) (a : Prop) (s : Signed) (i)

def docket (P : Keepat (C.side k p)) : SourceAt G ζ:= by
  let X:= boxat N k i p v P
  have hp:= freeat v h hk hN i (s:=0) P
  refine fulcrum x (X:=swath s (ζ x) P.val) ?_ (dot a∘ X∘pull s (ζ x)) (b:=0) ⟨?_, (dot_meas _).comp ((hp.meas).comp (continuous_pull ..|>.measurable)),?_⟩
  · simpa only [affine,Signed.act_zero,zero_add] using (stay s (ζ x) _|>.2 P.property)
  · exact fun k U=>congr_arg (dot a) (p_invar s (ζ x) hp.inv k U)
  exact fun U V hv=> congr_arg (dot a) (p_local s (ζ x) _ hp.locally _ _ hv)

include h hk hN
lemma portion (U : Config G (C.side k p)) :
    ∑ j,(docket i v h hk hN x a s (ζ:=ζ) j).amount (C.path.rep N p k).p.threshold U= Poly.send (slot x) (dot a (glare v i k N p (pull s (ζ x) U))):= by
  let P:= C.path.rep N p k; let t:=P.p.threshold
  let A:=wideX C v i k N p
  have hx:= (receipts C i h hk hN v p).2
  let X (j:wideIndex C v i k N p):Keepat (C.side k p) :=⟨A j,hx.anchored j⟩
  let V':= pull s (ζ x) U
  let F:=fun j=> wideW C v i k N p j * masked t (A j) (wideA C v i k N p j) V'
  obtain ⟨c,hχ,hv⟩:=hx.pays
  have hf : Summable F:= by
    refine hv.2.1.of_norm_bounded fun i=>?_ ; unfold F; rw [norm_mul]; apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    by_cases hh : Healthy t (A i) V'
    · rw [masked_eq _ _ _ _ hh]; exact (hχ i).2.2 V' hh [] (Nat.zero_le _) (by simp)
    rw [masked_ne _ _ _ _ hh,norm_zero]; exact (hχ i).2.1
  let G P:= masked t P.val (boxat N k i p v (P : Keepat _)) V'
  have he P : G P= ∑' i,if X i=P then F i else 0:= by
    by_cases hp : Healthy t P.val V'
    · unfold G; rw [masked_eq _ _ _ _ hp]; apply tsum_congr; intro j; by_cases hy:A j=P.val
      · have hz:= Subtype.ext (show (X j).val=P.val from hy); rw [if_pos (show wideX _ _ _ _ _ _ _=_ from hy),if_pos hz]; unfold F; rw [masked_eq t (A j) _ _ (hy.symm ▸ hp)]
      rw [if_neg (show wideX _ _ _ _ _ _ _≠_ from hy),if_neg (fun he=> hy (congr_arg Subtype.val he))]
    unfold G; rw [masked_ne _ _ _ _ hp]; symm; refine (tsum_congr (g:=fun _=>0) ?_).trans tsum_zero; intro j; split
    · rename_i hx'; unfold F; rw [masked_ne _ _ _ _ (show ¬ Healthy t (A j) V' from (show A j=P.val from congr_arg Subtype.val hx').symm ▸ hp),mul_zero]
    rfl
  let u:=univ (α:=Keepat (C.side k p))
  have hM (b : Finset (Keepat (C.side k p))) : ∑ j∈b,(docket i v h hk hN x a s (ζ:=ζ) j).amount (C.path.rep N p k).p.threshold U=
       Poly.send (slot x) (dot a (∑ j∈b,G j)):= by
    induction b using Finset.induction_on with
    | empty=> simp only [sum_empty,dot_zero,Poly.send_zero]
    | insert j b hi ih => rw [sum_insert hi,ih,sum_insert hi, dot_add, send_plus]; congr 1; apply congr_arg (Poly.send _); exact (pr_dot s (ζ x) a U _ t _).symm
  change (∑ i∈u,_)=_
  rw [hM]; apply congr_arg (Poly.send _); apply congr_arg (dot a);simp_rw [he]; exact pack_complex F X hf

-- tally long rents charging after k
omit h hk hN in
lemma lost (i k N p : ℕ) (hp : C.Makes) (h₁ : C.ref d ≤ k) (h₂ : k ≤ N) :
    let P:= (C.path.rep N p k).p
    ∃ c : wideIndex C v i k N p→ℝ,(∀ j,P.supBounds 0 (wideX C v i k N p j) (wideA C v i k N p j) (c j)) ∧ SumBudget (fun j=>P.mass (wideX C v i k N p j) (‖wideW C v i k N p j‖*c j)) (moneys C d k N p v) := by
  intro Q
  obtain ⟨a,b,ha,hb,H,h,x,hg⟩ := (hp.calibrated d N p (h₁.trans h₂)).cap k h₁ h₂ ((C.factory d N p).terminal.symm v)
  obtain ⟨u,hp,hu⟩:= x
  let D:=C.labels.level d; let K:= parcel C d k N p v;let f j:= Q.mass (K.support j) (u j)
  let A :=setOf (smalls C i k N p v); let s:= pinHat C d k; let m:= (C.path.levels.params k).columns
  have hx : (∑' j:↥(Aᶜ), f j.val)≤m*D.coeffSize K.x := by
    apply (le_trans (hp.2.1.tsum_subtype_le f Aᶜ hp.1) hp.2.2).trans
    exact ((le_add_of_nonneg_right hb).trans H).trans (mul_le_mul_of_nonneg_left (rotate_core D K.x) (zero_le_one.trans (C.path.levels.params k).columns_ge))
  have hc(v:wideIndex C v i k N p): Q.mass (K.support v.val) (‖s‖*u v.val)= ‖s‖*f v.val:=mul_left_comm ..
  let e : wideIndex C v i k N p →ℝ:=fun j=> ‖s‖*f j.val; have he : Summable e:= (hp.2.1.subtype Aᶜ).mul_left _
  refine ⟨fun j=> u j.val,fun j=> hu _, ?_⟩
  convert (show SumBudget e (moneys ..) from ⟨fun j=> mul_nonneg (norm_nonneg _) (hp.1 _),he,?_⟩) using 1
  · ext j; exact hc _
  unfold e; rw [tsum_mul_left]
  apply le_trans _ (le_refl (moneys C d k N p v)); apply (mul_le_mul_of_nonneg_left hx (norm_nonneg s)).trans_eq
  change _=m*(∑ i,‖(s • K.x) i‖); simp_rw [Pi.smul_apply,norm_smul,← mul_sum]; exact mul_left_comm ..

lemma long_cost (y : ℝ) {q : BudgetPoint} (P:=(C.path.rep N p k).p) (hp : P=(C.path.rep N p k).p) (H : Lower P q) (he : 0≤ y) (hf : scalesExp P q (2*y))
    (r : V→ℝ) (hr : 0 ≤ r x) :
    let E:= docket i v h hk hN x a s (ζ:=ζ)
    ∃ c : Keepat (C.side k p)→ℝ, (∀ j,transported (E j) P.threshold r (c j))∧ (∑ j,c j * debt q.B y (halo 8 (E j).extent)) ≤
      Real.exp (100000*y)* Real.exp (-(P.supportExponent*i)/2) * (r x*moneys C d k N p v) := by
  subst P; intro E
  let P:= (C.path.rep N p k).p; let Z:= wideX C v i k N p
  obtain ⟨c',hc',hE⟩:= lost v i k N p h hk hN
  let m j:= ‖pinHat C d k‖*c' j
  let f j:= P.mass (Z j) (m j)
  have ht : 0<P.threshold:=P.threshold_pos
  have hu k : 0 ≤ m k:= mul_nonneg (norm_nonneg _) (hc' _|>.1)
  have hs : Summable m := hE.2.1.of_nonneg_of_le hu fun i=> P.loMass (Z i) (m i) (hu i)
  have ha:= (receipts C i h hk hN v p).2.anchored
  let K j:Keepat (C.side k p):=⟨Z j,ha _⟩
  let cost (x : Keepat (C.side k p)):=∑' i,pay m (fun j=> K j=x) i
  have hH (x : Keepat (C.side k p)) : 0≤cost x:= by apply tsum_nonneg;intro j; unfold pay; split;exact hu _;exact le_rfl
  have hh (x) (U) (H : Healthy P.threshold x.val U) : ‖boxat N k i p v x U‖≤cost x:= by
    let F:=fun j=> if Z j=x.val then wideW C v i k N p j*wideA C v i k N p j U else 0
    let L j:=pay m (fun j=> K j=x) j
    have hf j: ‖F j‖≤ L j:= by
      unfold F L pay; by_cases h:Z j=x.val
      · rw [if_pos h,if_pos (Subtype.ext h),norm_mul]; exact mul_le_mul_of_nonneg_left (hc' j|>.2 U (show Healthy _ (Z j) U from h.symm ▸ H) [] (Nat.zero_le _) (by simp)) (norm_nonneg _)
      rw [if_neg h,norm_zero,if_neg (fun he=>h (congr_arg Subtype.val he))]
    have hl : Summable L:= hs.indicator (s:={j|K j=x}); have hm:= hl.of_nonneg_of_le (fun j => norm_nonneg (F j)) hf
    exact (norm_tsum_le_tsum_norm hm).trans ((hm.tsum_le_tsum hf hl).trans le_rfl)
  refine ⟨fun j=> r x * cost j,fun j=> (transferD ..).2 ⟨mul_nonneg hr (hH _),fun U hf=>?_⟩,?_⟩
  · change Poly.toll r (slot x)* ‖dot a _‖≤_; rw [Poly.solo_toll,dot_norm]
    exact mul_le_mul_of_nonneg_left (hh j _ ((s_healthy s (ζ x) ..).2 hf)) hr
  let A:=Real.exp (100000*y); let B:=Real.exp (-(P.supportExponent*i)/2)
  let d1 j:=debt q.B y (halo 8 (Z j))
  have heS j:d1 j ≤ A*Real.exp (P.supportExponent*coverNumber P.B (Z j)/2) := by
    have hV:=scaler P q H hf (show 0≤2*y by positivity) (Z j); change debt _ _ _ ≤ _ at hV
    unfold debt at hV; rw [← Real.exp_add, Real.exp_le_exp] at hV
    unfold A; rw [← Real.exp_add]; apply Real.exp_le_exp.mpr; linarith only [hV]
  have hz j: m j*d1 j ≤ A*B*f j := by
    apply (mul_le_mul_of_nonneg_left (heS j) (hu j)).trans
    let b:= (coverNumber P.B (Z j):ℝ)
    have hx : (i:ℝ) ≤ b:= by unfold b; exact_mod_cast Nat.le_of_lt (show i<coverNumber P.B (Z j) from lt_of_not_ge j.property)
    have hy : Real.exp (P.supportExponent*b/2) ≤ B*Real.exp (P.supportExponent*b):=by unfold B; rw [← Real.exp_add]; apply Real.exp_le_exp.mpr; linarith only [mul_le_mul_of_nonneg_left hx P.exponent_pos.le]
    apply (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hy (Real.exp_pos _).le) (hu j)).trans_eq
    dsimp only [b,A,B,f,BudgetPoint.mass]; ring
  let t j:=m j*d1 j; have H1 j:0≤t j:=mul_nonneg (hu _) (Real.exp_pos _).le
  have H2: Summable (fun j=> A*B*f j) := hE.2.1.mul_left _
  have H3 : Summable t:= H2.of_nonneg_of_le H1 hz
  have hD : ∑' j,t j≤ A*B*moneys C d k N p v:= by refine (H3.tsum_le_tsum hz H2).trans ?_; rw [tsum_mul_left]; exact mul_le_mul_of_nonneg_left hE.2.2 (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
  have H4 (j) : cost j*debt q.B y (halo 8 (E j).extent)=∑' i,pay t (fun i=> K i=j) i:= by
    change cost j*debt q.B y (halo 8 (swath s (ζ x) j.val))=_
    rw [← swath_iffHalo, debt,swath_cover]; unfold cost; rw [← tsum_mul_right]; refine tsum_congr fun v'=>?_
    unfold pay;split_ifs with he; rw [← he]; rfl
    rw [zero_mul]
  simp_rw [mul_assoc (r x),H4]; rw [← Finset.mul_sum, pack_all _ K H3]
  exact (mul_le_mul_of_nonneg_left hD hr).trans_eq (mul_left_comm ..)
end
end YM.Next.Rank.Edition
