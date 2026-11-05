import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Yield
import YM.Extra.MULTISOURCE_BOUNDS.Merger
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Opacity.Desk
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Opacity.Ferry
/-!
# Ticketing powder through Frco / chain price. *Actual* Q; retain coherence with Fsct pieces
Only value Petty and real headings here. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Pump.Port
open Function Lattice RG Pressure Pressure.Tube Pressure.Stores Tree Wilson
open Matrix Finset PhysicalGuard7f546.Curved Next.SectorChange Precision AnalyticBridge.LocalGaussianLaws Filter
    SectorTools.PhysicalGaussianSwitch AnalyticBridge.RelativeLogdet MeasureTheory
    Push.SectorMeasure Push.SectorMeasure.Presented Push.SectorMeasure.Oriented Native Gaussian GaugeRoute Physical
    AnalyticBridge.MarginalMultiplier3b1d PatchReads Rows Wisps Display Display.Docking Display.Sew  Push.AbsoluteSums
    AnalyticNext.ConnectedActivity Milk Dictionary Dictionary.Notify Wires Barge EndpointLoadF16.DetLong Print Completion
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius Completion
variable {c f : Side} {G : Gauge} {S : StepData c f} {P : Teller G} {x y W a e g L η C b d : ℝ} {p q : Pilot G S x} {X : Support c} {v : Dyed G S}
local notation "N"=>Physical.Key G f
local notation "J"=>Physical.place S (G:=G)
local notation "A"=>radiusB x
private def passenger (ξ : Type): ((ξ×ξ) × Sequence ξ) ≃ Trip ξ where
  toFun a:= ⟨a.2.1,a.1.1,a.1.2,a.2.2⟩
  invFun a:= ((a.2.1,a.2.2.1),⟨a.1,a.2.2.2⟩)
  left_inv _:=rfl
  right_inv _:=rfl

def soapy (p:Pilot G S x) (i:N):= (backdrop x p.key p.park p.y).2 i.1 i.2
def toll (v : Dyed G S) (T : Trip N) (p:Pilot G S x):=
    let i:=T.2.1; let j:=T.2.2.1
    soapy p i * forward (Wires.beam v.things p.tag p.view x p.key p.park) (cloudX v.things x p.tag p.view p.key p.park) i j ⟨T.1,T.2.2.2⟩ * soapy p j / 2
lemma doggy (p:Pilot G S x) (i:In x p.key p.park (G:=G)) : soapy p (sorted p.key p.park (.inl i))=p.y.2 i:=congr_fun (congr_arg Prod.snd (rollback x p.key p.park p.y)) i
lemma zeroY (p:Pilot G S x) (i:vacant p.key p.park x G): soapy p (sorted p.key p.park (.inr i))=0:= by
  rw [sorted_last]; unfold soapy backdrop fresh; dsimp only; split
  next ht=> split
            next he=> let a: Active p.key x p.park:=⟨⟨_,ht⟩,he⟩; exact (i.property ⟨(a,i.val.2), Prod.ext rfl rfl⟩).elim
            rfl
  rfl
private lemma transite {α β : Type} [Fintype α] [Fintype β] (h : Equiv β α) (i : α→ℝ) (B : Matrix β β ℝ) : i ⬝ᵥ (B.submatrix h.symm h.symm*ᵥ i) = (i ∘ h) ⬝ᵥ (B *ᵥ (i∘h)):= by
  unfold mulVec dotProduct; rw [← Equiv.sum_comp h]; refine sum_congr rfl fun j _=> ?_
  apply congr_arg (i (h j)* ·); change (∑ k, B (h.symm (h j)) (h.symm k)*i k) =∑ k, B j k*(i ∘ h) k; rw [← Equiv.sum_comp h]; apply sum_congr rfl; intro k hk; simp
set_option maxHeartbeats 500000 in
lemma voyage (hc : Certified S v.things x g C η b) (hC : Boosted v.things P x) (hp : Matched p) :
    let W:= Rows.gram v.things x p.view p.tag (shots S x) p.key p.park; let D:= fog p.key p.park v.things x p.view p.tag; let z:= p.y.2
    HasSum (fun T:Trip N=>toll v T p) ((z ⬝ᵥ ((D⁻¹-W)*ᵥ z))/2):= by
  intro W D z; let a:=p.key; let F:=p.park; let T:=v.things
  let t i j:=forward (Wires.beam T p.tag p.view x a F) (cloudX T x p.tag p.view a F) i j
  obtain ⟨b,hK⟩:= hC.license p.key p.park p.view hp
  let N':=Wires.beam T p.tag p.view x a F; let P':=cloudX T x p.tag p.view a F
  obtain ⟨h₁,h₂,hP,h5⟩:= hc.text a F p.tag p.view hp
  have hz : IsUnit D.det:=isUnit_iff_ne_zero.mpr hP.det_pos.ne'
  have hx:P'=CFull T a F x p.view p.tag:= cloudX_exact T _ hC.produced _ _ a F hK hc.precision h₁
  let C':=wide D (1:Gaussian.Table (vacant a F x G)); let L:=sorted a F (x:=x) (G:=G)
  have he₁:N'=(wide W (1:Gaussian.Table (vacant a F x G))).submatrix L.symm L.symm:=Wires.beam_exact _ _ _ _ _ _ hC.produced hK
  have he₂:P'⁻¹=(Completion.wide D⁻¹ (1:Gaussian.Table (vacant a F x G))).submatrix L.symm L.symm:= by
    rw [show P'=C'.submatrix L.symm L.symm from hx]
    have hv : (wide D (1:Gaussian.Table (vacant a F x G)))⁻¹=wide D⁻¹ 1:=by convert! (Completion.wide_id_inv D (β:=vacant a F x G) hz)
    refine (sub_inv C' L.symm ?_).trans (congr_arg (fun z : Matrix _ _ ℝ => z.submatrix L.symm L.symm) hv)
    apply isUnit_iff_ne_zero.mpr; have hC : C'.det=D.det* (1:Gaussian.Table (vacant a F x G)).det := by convert! (wide_det D (1:Gaussian.Table (vacant a F x G)))
    rw [hC,Matrix.det_one,mul_one]; exact hP.det_pos.ne'
  have hS : soapy p ∘ L ∘ Sum.inl=z:=funext fun i=>doggy p i
  have h0 : soapy p ∘ L ∘ Sum.inr=0:=funext fun i=>zeroY p i
  have he : soapy p ⬝ᵥ ((P'⁻¹-N') *ᵥ soapy p) = z ⬝ᵥ ((D⁻¹-W) *ᵥ z) := by
    rw [he₁,he₂,Matrix.sub_mulVec,Matrix.sub_mulVec,dotProduct_sub,dotProduct_sub,transite,transite,wide_cost,wide_cost]
    simp_rw [Function.comp_assoc,h0,hS]; simp
  let t':=passenger N; let F' (i:N×N) (j:Sequence N):= toll v (t' (i,j)) p; let τ i:= soapy p i
  let F'' (i:N × N):= τ i.1*(P'⁻¹-N') i.1 i.2*τ i.2 / 2
  have hg (i:N×N) : HasSum (F' i) (F'' i):= ((((award p.tag hC hp hc).1 i.1 i.2).mul_left (τ i.1)).mul_right (τ i.2)).div_const _
  apply (t'.hasSum_iff).1; let u:= uncurry F'
  have hl : (∑ i,F'' i)=(z ⬝ᵥ ((D⁻¹-W)*ᵥ z))/2:= by rw [Fintype.sum_prod_type,← he]; unfold mulVec dotProduct F''; simp_rw [Finset.sum_div,Finset.mul_sum]; exact sum_congr rfl fun i _=> (by rw [Finset.sum_div]; apply sum_congr rfl; intro j hj; change τ i * _ * τ j / 2 = _; unfold τ; ring)
  rw [← hl]
  have hs : Summable fun p => |u p|:= (summable_prod_of_nonneg (fun p => abs_nonneg (u p))).2 ⟨fun i=>(hg i).summable.abs,Summable.of_finite⟩
  have hθ:Summable u:= Summable.of_norm hs; change HasSum u _; apply hθ.hasSum_iff.mpr
  rw [hθ.tsum_prod]; simp_rw [show ∀ i:N×N, (∑' j,u (i,j))=F'' i from fun i=> (hg i).tsum_eq]; exact tsum_fintype _
lemma backLens {α : Type} {i j:α} (X:α→ Site c) {l B : ℕ} {k} (w:Fin k→α) : lens X l B j ⊆ pocket X l B i j w:= by
  induction k generalizing i with
  | zero=> exact subset_union_right
  | succ k ih=> exact (ih (i:=w 0) (Fin.tail w)).trans subset_union_right
lemma bulge {α : Type} {i j:α} (X:α→ Site c) {l m B : ℕ} {k} (w:Fin k→α) (h : l ≤ m) : pocket X l B i j w⊆pocket X m B i j w:= by
  have hm i:lens X l B i⊆lens X m B i:= Corona.halo_mono (Nat.mul_le_mul_right B h) (Finset.Subset.refl _)
  induction k generalizing i with
  | zero=> exact union_subset_union (hm i) (hm j)
  | succ k ih=> exact union_subset_union (hm i) (ih _)
lemma soap_read (hc:Boosted v.things P x) (i:N) (he:lens J 40 A i⊆X): Pulled (fun p=>soapy p (G:=G) (S:=S) (x:=x) i) X:= by
  refine ⟨fun B F k=>?_,fun p q H M h=>?_⟩
  · refine ⟨fun a=> (Print.backdrop x B F (G:=G) a.2).2 i.1 i.2,?_,fun _ _ _=>rfl⟩
    have he:= (recording (G:=G) x B F).snd
    exact ((show Continuous (fun y:G.Color=> y i.2) from PiLp.continuous_apply ..).measurable.comp ((measurable_pi_apply i.1).comp he)).comp measurable_snd
  have hx : Shields X (S.ratio.parent i.1.1) (22*A):=(Shields.full J i 40 A he).shrink (by omega)
  exact congr_arg (fun y:G.Color=>y i.2) (glance hc.produced.scale h hx).2
lemma toll_read (hc:Boosted v.things P x) (i:Trip N): Pulled (toll v (x:=x) i) (berth J 40 A i) := by
  obtain ⟨i,j,l,w⟩:=i
  have ht := soap_read (X:= pocket J 40 A j l w) hc j (first_lens ..); have hm := soap_read (X:= pocket J 40 A j l w) hc l (backLens ..)
  refine ((ht.times (v:=fun p:Pilot G S x=> Dictionary.Notify.forward (Wires.beam v.things p.tag p.view x p.key p.park) (cloudX v.things x p.tag p.view p.key p.park) j l ⟨i,w⟩) ?_).times hm).twine (measurable_id.div_const _)
  refine ⟨fun B F k=>?_,fun p q _ _ h=>forward_law _ hc.produced _ _ _ (bulge _ _ (by omega)) h.reads⟩
  exact ⟨_,(Typeset.lead (fun i j=>beam_meas v.things k x B F i j hc.produced.branched) (fun i j=> cloudX_meas v.things _ _ _ _ hc.produced.branched i j) j l _).comp measurable_fst,fun _ _ _=>rfl⟩
end YM.PhysicalNext.InteractingRank.Pump.Port
