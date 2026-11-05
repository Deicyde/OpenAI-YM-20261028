import YM.RG08.Pivot.Danes

set_option autoImplicit false
noncomputable section
namespace YM.RG08.Pivot
open Function Filter Lattice Wilson RG Exterior Precision Next.Free
open Laurent Bloch Matrix Work.F08 Tree FreeResolvent Stationary Finset
open UVExt.Paths Drift Scores Loom Shade Quire Tall Vale Analysis Push.AbsoluteSums
open scoped Topology BigOperators Classical
variable {α E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {r k n : ℕ}
-- Point estimates. Also exact on periodic general (bounded) K.
variable {K P: Row α α} {U V : Quire.Rooted E α (r+2)} {B κ A:ℝ} {v : Cover × α→ℝ}
def Plaque (K:Row α α)(B:ℝ):Prop := 0≤B ∧ ∀ i j z, ‖K i j z‖ ≤ B
omit [CompleteSpace E] in
lemma Fink_tap (h:Plaque K B)(hp : Pens U) : Pens (knot none U K) := by
  apply Summable.of_nonneg_of_le (fun i=> norm_nonneg _) _ (hp.mul_left B); intro i; unfold knot; rw [norm_smul]
  exact mul_le_mul_of_nonneg_right (h.2 _ _ _) (norm_nonneg _)
lemma disciples (f : Quire.Rooted E α (r+2))(h:Pens f)(hp:Plaque K B) : Tidy (jib none K f):= Tidy.sewn (((Fink_tap hp h).pours _).scale _)
lemma fil_tax (h: Ink (brocade v) U A)(ht:1≤v)(hp:Plaque K B): Ink (brocade v) (jib none K U) (‖batting r‖*(B*A)) := by
  refine sewn_income _ (show 0≤_ from fun i=>zero_le_one.trans (fineBro ht i)) (fun u s=> Equiv.prod_comp s (fun i=>v (u i))) (Ink.scale (Ink.pour stems ?_ (fineBro ht)) _)
  refine budget_mono (budget_scale hp.1 h) (fun i=> mul_nonneg ((fineBro ht (stems i)).trans' zero_le_one) (norm_nonneg _)) ?_
  intro i; simp only [knot,norm_smul,Function.comp_apply]; rw [←mul_assoc,←mul_assoc]; refine mul_le_mul_of_nonneg_right (le_trans (mul_le_mul ?_ (hp.2 _ _ _) (norm_nonneg _) ((fineBro ht i).trans' zero_le_one)) (le_of_eq (mul_comm ..))) (norm_nonneg _)
  have he {a:ℕ} (p:Beads α (a+1)) : brocade v (stem1 p)≤ brocade v p := by
    unfold brocade; conv_rhs=> rw [Fin.prod_univ_succ]
    exact le_mul_of_one_le_left ((fineBro ht _).trans' zero_le_one : 0≤brocade v (stem1 p)) (ht _)
  exact (he (stem1 i)).trans (he i)
lemma fil_pol (h:Polished U)(hp:Plaque K B): Polished (jib none K U) := by
    intro k; obtain ⟨a,h⟩:=h k; exact ⟨_,fil_tax (v:=fun i=> dime k i.1) h (fun _=> Planned.PrimaryIntegral295.Carrier.liftCost_ge ..) hp⟩
lemma fil_exp (h:Quire.Lit U κ A)(ht:0≤κ)(hp:Plaque K B): Quire.Lit (jib none K U) κ (‖batting r‖*(B*A)) := by
    unfold Quire.Lit Quire.Ink at *
    simp_rw [bro_lit] at h ⊢; exact fil_tax h (fun i=> Real.one_le_exp (mul_nonneg ht (by positivity))) hp
lemma phil_less (ha : Plaque K B) (h:Pens U)(hp:Pens V): jib none K (U-V)=jib none K U-jib none K V:= by
    unfold jib; rw [show knot none (U-V) K=knot none U K-knot none V K from funext fun i=> smul_sub .., Pens.tub_sub stems (Fink_tap ha h) (Fink_tap ha hp),smul_sub,sew_sub]
lemma phil_bet (h:Pens U) (hp:Plaque K B)(hx:Plaque P A): jib none (K-P) U=jib none K U-jib none P U := by
    unfold jib; rw [show knot none U (K-P)=knot none U K-knot none U P from funext fun i=>sub_smul ..,Pens.tub_sub stems (Fink_tap hp h) (Fink_tap hx h),smul_sub,sew_sub]
lemma phil_nil (hp:Plaque K B): jib none K (0:Quire.Rooted E α (r+2))=0:= by simpa only [sub_self] using phil_less hp (Pens.zero _ E : Pens (0:Quire.Rooted E α (r+2))) (Pens.zero ..)
-- echo
omit [CompleteSpace F] in
lemma phil_echo (h:Pens U)(hp:Plaque K B)(q : E→L[ℝ] F): q ∘ jib none K U=jib none K (q∘U) := by
    unfold jib; rw [cast_sew,Pens.echo_pool _ (Fink_tap hp h),show q ∘ knot none U K=knot none (q ∘ U) K from funext fun i=> map_smul ..]

lemma fills_cut {m:ℕ → Row α α}{U:ℕ→Quire.Rooted E α (r+2)}(hk:Tendsto m atTop (𝓝 K))(hx:∀ i,Plaque (m i) B) (hp:Plaque K A) (h:Hurled U V):
    Hurled (fun i=> jib none (m i) (U i)) (jib none K V) := by
  have he i : Tidy (jib none (m i) (U i)) := disciples _ (h.ever _) (hx _)
  have hA: Tidy (jib none K V) := disciples _ h.old hp
  have hz : Hurled (fun i=>jib none (m i) V) (jib none K V) := by
    refine ⟨hA.pens,?_⟩
    let S i:=knot none V (m i)-knot none V K; let v i:=∑' j, ‖S i j‖
    have hv i: Pens (S i) := Pens.less (Fink_tap (hx i) h.old) (Fink_tap hp h.old)
    have hh : Tendsto v atTop (𝓝 0) := by
      have hr i : Tendsto (fun j=> ‖S j i‖) atTop (𝓝 0):= by
        have hm : Tendsto (fun j=> tuneS (m j) none i) atTop (𝓝 (tuneS K none i)) := tendsto_pi_nhds.mp (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hk _) _) _
        simpa only [sub_self,norm_zero] using! ((hm.smul_const (V i)|>.sub (tendsto_const_nhds (x:=tuneS K none i • V i))).norm)
      have ht (i j) : ‖S i j‖ ≤ (B+A)*‖V j‖ := by
        apply (norm_sub_le ..).trans; unfold knot; simp only [norm_smul]; rw [add_mul]; exact add_le_add (mul_le_mul_of_nonneg_right ((hx i).2 _ _ _) (norm_nonneg _)) (mul_le_mul_of_nonneg_right (hp.2 _ _ _) (norm_nonneg _))
      simpa using tendsto_tsum_of_dominated_convergence (h.old.mul_left (B+A)) hr (Eventually.of_forall fun i j=> by rw [norm_norm]; exact ht i j)
    refine ⟨_,(show Tendsto (fun i=> ‖batting r‖*v i) atTop (𝓝 0) from by simpa using hh.const_mul _),fun i=>?_⟩
    unfold jib; rw [← sew_sub,← smul_sub,← Pens.tub_sub stems (Fink_tap (hx i) h.old) (Fink_tap hp h.old)]
    refine stitching (Ink.scale (Ink.pour stems ?_ (ling_one le_rfl)) _)
    rw [show ling 0 ∘ (stems (α:=α) (r:=r))=1 from funext fun i=>by simp [ling]]; exact (hv i).priced
  let Q i:= jib none (m i) (U i - V)
  have hh : Decline Q := by
    obtain ⟨A,ha,H⟩:= h.moment.thus; refine ⟨_,(show Tendsto (fun i=> ‖batting r‖*(B*A i)) atTop (𝓝 0) from by simpa using (ha.const_mul B).const_mul _),fun i=> fil_exp (H i) le_rfl (hx _)⟩
  refine ⟨hA.pens,?_⟩; convert hh.plus hz.moment using 1
  funext i; simp only [Pi.add_apply,Q,phil_less (hx i) (h.ever i) h.old]; abel

end YM.RG08.Pivot
