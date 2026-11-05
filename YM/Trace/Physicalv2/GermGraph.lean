import YM.Trace.Physicalv2.Germ
import YM.ProjectorNext.PROJECTOR_EQUIVARIANCE.Fringe
import YM.MultiNext.SIGNED_SOURCE_CONTINUATION.Factory
import YM.MergeProof.Biscuit

/-! One literal-mark physical primary/stable graphs, for use with represented
models of the inserted density (not its pointwise conditional quotient). Orbit
costs in `Tones` are all on the *same* representation with its actual vacuum
and inventory; these proofs make no assertion about superposition of different
vacuum layers or simultaneous collision estimates. Only a local-comparison
component. -/
noncomputable section
namespace YM.Trace.Physical.GermGraph
open Function Set Filter Labels Lattice Wilson RG Source Analysis Next.Foundations
open Push.Local ProjectorNext.Equivariance MeasureTheory Extra.Histories Relay
open Germ Bid Work.G08 PhysicalNext.Repeat.Lotus YM.MergeProof
open PhysicalNext.Repeat.Legato.Bandage
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 3600000
set_option synthInstance.maxHeartbeats 125000
set_option quotPrecheck false
set_option warningAsError false
set_option maxRecDepth 3600
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

variable {G:Gauge}{C:Family G}(d:ℕ)(N p m:ℕ)

abbrev stage (C:Family G)(m:ℕ):= C.path.levels.params m
abbrev plank (C:Family G)(m:ℕ):= C.path.levels.budget m
abbrev safety (C:Family G)(m:ℕ):= Real.sqrt (C.path.levels.clock.forcedAllowance m)
abbrev stock (C:Family G)(m:ℕ):= (stage C m).columns
abbrev factor (C:Family G)(m:ℕ):= ((C.S.block m).val:ℝ)
local notation "F" => C.labels.level
local notation "R!" => C.path.rep
local notation "ent" => (C.factory d N p).entries
abbrev page (q:Coefficient (F d) (C.side m p)):C.label d:= projection (F d) C.params (plank C m).threshold 0 q
abbrev price : ℝ := (((F d).extra+1:ℕ):ℝ)*(Germ.germ_close (F d) C.params).choose
abbrev cut :ℝ:= wraps (plank C m) (C.side m p)
abbrev invoice (d m p : ℕ) :ℝ := price (C:=C) d * cut (C:=C) p m
abbrev reads (q:Coefficient (F d) (C.side m p))(r : ℝ):Prop:= q.Format 0 C.params (C.path.rep N p m) ∧ q.remBound 0 (C.path.rep N p m) (safety C m) r
structure Opened (C:Family G)(d m p:ℕ) : Prop where
    post : C.ref d ≤ m
    small : invoice (C:=C) d m p*(stock C m) < 1/4
lemma add_projection {n : Side}{R:Rep G n}{o:Site n}{F₀:Labels.Frame G d}{A : Hol G}(q v:Coefficient F₀ n)(hq:q.Format o A R)(hv:v.Format o A R) (hd:d≤R.p.order)(hp:d≤R.p.power)(eq:∃κ r,q.remBound o R κ r)(ev : ∃ κ r, v.remBound o R κ r):
      let P := Germ.projection F₀ A R.p.threshold o
      P (beside q v) = P q + P v := by
    intro P
    let T:Bool×ℕ→F₀.Coeff:=fun ⟨i,j⟩=> vector F₀ A R.p.threshold o ((twain q v i).regular j)
    have hz(i : Bool): Summable (Function.curry T i) := by
        let Y:=twain q v i
        have hi : Y.Format o A R ∧ ∃ C r,Y.remBound o R C r := by cases i; exact ⟨hv,ev⟩; exact ⟨hq,eq⟩
        obtain ⟨H,κ,r,hb⟩:=hi
        -- use summability via tsum cost? private lemma! Reprove or expose
        exact Germ.vector_summable F₀ A H hb hd hp
    have ht : Summable T:=Summable.of_norm (summable_prod_of_nonneg (fun i=>norm_nonneg _) |>.mpr ⟨fun i=> (hz i).norm,Summable.of_finite⟩)
    unfold P Germ.projection; rw [reckon]
    have hs := (code Bool).tsum_eq T
    rw [ht.tsum_prod' hz, tsum_fintype (β:=Bool),Fintype.sum_bool] at hs
    rw [show ∑' i,vector F₀ A R.p.threshold o ((beside q v).regular i) = _ from hs]
    change q.x+v.x+((∑' i,vector F₀ A R.p.threshold o (q.regular i)) + ∑' i,vector F₀ A R.p.threshold o (v.regular i)) = _; abel
lemma dimensions (H:C.Makes)(hp:C.ref d ≤ m)(h:m ≤ N): d≤(R! N p m).p.order ∧ d≤(R! N p m).p.power:=by obtain he:=(H.stages d).2 _ hp; have hz:=(H.wilson.represents N p m h).vac; rw [hz]; exact ⟨by exact le_trans (Nat.le_succ d) he.1,he.2⟩
lemma entryOk (H:C.Makes)(hp:C.ref d ≤ m)(h:m ≤ N) (x:C.label d): reads d N p m (ent m x) ((stock C m)* (F d).coeffSize (ent m x).x) := by
    have he:= H.calibrated d N p (hp.trans h); refine ⟨he.format _ hp h x,?_⟩; obtain ⟨a,b,ha,hb,hab,hκ,W,X⟩:=he.cap _ hp h x; exact ⟨a,b, ha,hb,hab.trans (mul_le_mul_of_nonneg_left (size_core _ _) (zero_le_one.trans (stage C m).columns_ge)),hκ,W,X⟩
lemma measured_diff {q:Coefficient (F d) (C.side m p)}(H:C.Makes)(hp : C.ref d ≤ m)(h:m ≤ N){r:ℝ}(hq: reads d N p m q r): (F d).coeffSize (page d p m q-q.x) ≤ (invoice (C:=C) d m p) * r:= by
    calc _ ≤ (((F d).extra+1:ℕ):ℝ) * ‖page d p m q-q.x‖ := size_le_norm ..
         _ ≤ _ := ?_
    have hv: (R! N p m).p=plank C m:= (H.wilson.represents _ _ _ h).vac
    have hz:= (Germ.germ_close (F d) C.params).choose_spec.2 (R! N p m) q hq.1 hq.2 (dimensions d N p m H hp h).1 (dimensions d N p m H hp h |>.2)
    rw [hv] at hz
    exact le_trans (mul_le_mul_of_nonneg_left hz (Nat.cast_nonneg _)) (le_of_eq (by unfold invoice price cut; ring))


local notation "cnt" => (C.labels.level d).coeffSize
local notation "x₀" => fun x:C.label d => (ent m x).x
lemma size_gap (H:C.Makes)(h:Opened C d m p)(hi : m ≤ N) (z:C.label d) : cnt (page d p m (ent m z)) ≤ 2*cnt ((ent m z).x) ∧ cnt ((ent m z).x) ≤ 2*cnt (page d p m (ent m z)) := by
    let x:= (ent m z).x
    let y:= page d p m (ent m z)
    have hz:= measured_diff d N p m H h.post hi (entryOk d N p m H h.post hi z)
    have h0 := Work.G08.size_nonneg _ x; have hy0 := Work.G08.size_nonneg _ (y-x)
    have h0y := Work.G08.size_nonneg _ y
    have hneg : cnt (x-y)=cnt (y-x):=by unfold Frame.coeffSize; apply Finset.sum_congr rfl; intro i _; exact norm_sub_rev ..
    have hl := le_trans hz (show _ ≤ (1/4:ℝ)*cnt x by rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right h.small.le h0)
    have hx:=Size.add (F d) x (y-x) |>.trans (add_le_add le_rfl hl)
    have hv:=Size.add (F d) y (x-y)
    rw [_root_.add_sub_cancel] at hx hv; rw [hneg] at hv
    change cnt y ≤ _ at hx; change cnt y≤2*cnt x ∧ cnt x ≤ 2*cnt y; constructor <;> linarith
lemma entry_isLinear (H:C.Makes)(h:Opened C d m p)(hi:m ≤ N) : IsLinearMap ℂ (fun x:C.label d=>page d p m (ent m x)) := by
   have hv: (R! N p m).p=plank C m:= (H.wilson.represents _ _ _ hi).vac
   have hs:= dimensions d N p m H h.post hi
   have hq (x):= entryOk d N p m H h.post hi x
   have ht:= (H.calibrated d N p (h.post.trans hi)).linear _ h.post hi
   simpa only [page,←hv] using Germ.linear_projection (F d) C.params (R:=R! N p m) (o:=0) (ent m) hs.1 hs.2 (fun i=>(hq i).1) (fun i=>⟨_,_,(hq i).2⟩) ⟨ht.1,ht.2.1⟩
noncomputable def fitting (H:C.Makes)(h:Opened C d m p)(hi:m ≤ N) : C.label d ≃ₗ[ℂ] C.label d := by
   let f: C.label d →ₗ[ℂ] C.label d := (entry_isLinear d N p m H h hi).mk' _
   apply LinearEquiv.ofBijective f
   have hx : Injective f := by
       apply LinearMap.ker_eq_bot.mp; refine LinearMap.ker_eq_bot'.mpr fun u hu=>?_
       have hz: (ent m u).x=0:= by
           have hZ:= (size_gap d N p m H h hi u).2
           rw [show page d p m (ent m u)=0 from hu] at hZ
           exact norm_le_zero_iff.mp ((norm_le_size ..).trans (by simpa only [Frame.coeffSize,Pi.zero_apply,norm_zero,Finset.sum_const_zero,mul_zero] using hZ))
       exact (MultiNext.SignedSource.matrices H h.post hi p).injective (((show MultiNext.SignedSource.matrices H h.post hi p u =_ from rfl).trans hz).trans (map_zero _).symm)
   exact ⟨hx,LinearMap.injective_iff_surjective.mp hx⟩
lemma fitting_apply (H:C.Makes)(h:Opened C d m p)(hi:m ≤ N)(x:C.label d): fitting d N p m H h hi x=page d p m (ent m x):=rfl
lemma graph_cost (H:C.Makes)(h:Opened C d m p)(hi:m ≤ N)(x:C.label d) : reads d N p m (ent m x) (2*stock C m*cnt (fitting d N p m H h hi x)):= by
    obtain ⟨hF,a,b,ha,hb,hab,r⟩:=entryOk d N p m H h.post hi x
    refine ⟨hF, a, b, ha,hb, hab.trans ?_,r⟩
    have hs := (stage C m).columns_ge; have hq:= mul_le_mul_of_nonneg_left (size_gap d N p m H h hi x).2 (zero_le_one.trans hs)
    change _ ≤ _* cnt (page d p m (ent m x)); linarith only [hq]
end YM.Trace.Physical.GermGraph
