import YM.RemainderComparison.Cascade.Main
import YM.RemainderComparison.Cascade.Choice
import YM.MergeProof.TeamFlow
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Daisy.Pint
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Lotus.Sofa

set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Cascade
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse
open Coat Matter ProbabilityTheory Poll Pond Mixed Census Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Shield Eider Flux Art Silica Poll Pond PhysicalNext.Repeat PhysicalNext.Repeat.Lotus
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ E Λ μ x κ w C : ℝ} {Ñ:ChartRatio G}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
variable (M:Team R)(X:Coat T F)(H:Cash W x μ L Q o C T R) (a' : ℝ) (u:ConnectedActivityE6.Alphabet c f→ℝ)
    {q A B b e a χ' v d:ℝ}{j n:ℕ}{χ:Chi} (Ξ : Utopia H j v d r q χ)
open Itinerary Animals
open Stained March
variable {Ξ:Utopia H j v d r q χ}(he : Seminar M H p j A χ e v)
    (Θ:Oboe H j v B n A b Ξ) (hx:X.x=x) (hF:X.χ=χ) (hk:X.width=o.K) (ht:Healthy (Pressure.temp x) (H.unionP p) X.V)(hm: (roster p).flags=∅)
section
variable {E:Type} [NormedAddCommGroup E] [NormedSpace ℝ E][FiniteDimensional ℝ E]{U:E→ Config G c} {y:E} (h: Mode U y j v)(hs:U y=X.V) (hB:0≤e)

local notation "P" => e
omit Θ he hx hF hk ht hm in
lemma stalk (ha:¬ M.signs S⊆p) : M.picture X p W a Ñ m=0:=by
  unfold Team.picture Team.grove; apply integral_eq_zero_of_ae; filter_upwards with x; split
  next _ => unfold likely Team.cinema Team.floret; simp_rw [if_neg ha,mul_zero, integral_zero,Finset.sum_const_zero,mul_zero]; rfl
  next => rfl
include Θ he hx hF hk ht hm h hs hB
lemma pistes : Brush j P 1 (fun z=> M.picture (vary X (U z)) p W o.a Q.table Q.halo) y:=by
  apply Brush.shimmy _ (M.arc X p H Θ hx hk hF hm ht h hs)
  have hP:0≤P:= hB
  by_cases ha:M.signs S⊆p
  swap
  · apply Brush.zi _ hP zero_le_one; filter_upwards [M.arc X p H Θ hx hk hF hm ht h hs] with z hz; rw [← hz]; exact stalk M _ ha
  have hR:= H.laws.data
  unfold Team.grove; simp_rw [show ∀ z: E, (vary X (U z)).B=radiusB x from fun z=> congr_arg radiusB hx]
  split_ifs with hX
  swap; · exact Brush.zi EventuallyEq.rfl hP zero_le_one
  let A' i:=(planted X p).taggedL i; let K:=H.unionP p; let I:=podium S G K (radiusB x); let f i z:= M.cinema ((preps (vary X (U z)) (roster p)).taggedL i) p W o.a Q.table Q.halo I
  have hY i : Brush j P 1 (f i) y:=by
    have hv:(A' i).manifest:=planted_valid X p
    have hh:=Θ.flow F (A' i) hx hF hk hv E U y hs h
    have hz:X.B=radiusB x:=congr_arg radiusB hx
    obtain ⟨g,hg,Hf,hQ⟩:= he E F (A' i) U y hF hv hx hk (hx.symm ▸ ht) hX.2 hX.1 ha h hs
    let Z:= A' i; have hℓ:8*o.a*Pressure.fiery G Z.x S.patch.L≤A/2:=by rw [show Z.x=x from hx,hR.funds.length_eq]; exact Θ.mode
    let I':=edgesM S K (radiusB x)
    have H': Cash W Z.x μ L Q o C T R:= (show x=Z.x from hx.symm) ▸ H
    have hK : (edgesM S (H'.unionP p) (Z.B))= I':=by unfold I'; change edgesM S (ground _ T Q.halo X.B p) X.B= _; rw [hz]; rfl
    apply Brush.shimmy ((M.boosts Z p H' hk hv I' hh Θ.conduit hℓ|>.1).buds g hg zero_le_one Hf (Filter.Eventually.of_forall hQ))
    filter_upwards [M.chutes Z p H' hk hv hh Θ.conduit hℓ] with z hz'
    unfold f; rw [← M.casin X p H hx hm ht i (U z) (U z) (fun _ _ _=>rfl), show (podium S G (H.unionP p) (radiusB x))=podium S G (H'.unionP p) Z.B from ?_]
    · rw [hK] at hz'; exact hz'
    change _=podium S G (ground _ T Q.halo X.B p) X.B; rw [hz]; rfl
  let l:ℝ:=Fintype.card S.Choices; have hp:0<l:=by unfold l; positivity
  apply ((Brush.spree _ f _ zero_le_one (fun i (_:i∈univ)=> hY i)).smul l⁻¹).climb _ le_rfl
  rw [sum_const,nsmul_eq_mul,card_univ,Real.norm_of_nonneg (inv_nonneg.mpr hp.le),inv_mul_cancel_left₀ hp.ne']
end
section
variable {Y C':ℝ}{H:Cash W x μ L Q o C T R}(N: Captain H j q d v Y A b r B C' n χ)
    (hh:Seminar M H p j A χ e v) (hX:X.x=x)(hZ:X.width=o.K)(hf:X.χ=χ)(hp:(roster p).flags=∅)
local notation "VP" => e
include hX hZ hf hp hh N
lemma luminos (hhp:0≤e) : M.bloom X W o.a Q.table Q.halo p=masked (Pressure.temp x) (H.unionP p) (fun y=> M.picture (vary X y) p W o.a Q.table Q.halo) X.V ∧
    (Healthy (Pressure.temp x) (H.unionP p) X.V→ Ore X.V (fun y=> M.picture (vary X y) p W o.a Q.table Q.halo) v VP j):=by
  rw [M.pictured X p H hX hZ hp]; constructor
  · by_cases h: Healthy (Pressure.temp x) (H.unionP p) X.V
    · have hx:= (M.arc X p H N.oboe hX hZ hf hp h (y:=(0:ℝ)) (show Mode (fun _:ℝ=> X.V) _ j v from ⟨N.position.le,fun i=> a_oneB G _ N.position.le⟩) rfl).self_of_nhds
      rw [masked_eq _ _ _ _ h,masked_eq _ _ _ _ h]; exact hx.symm
    rw [masked_ne _ _ _ _ h,masked_ne _ _ _ _ h]
  intro h E _ _ _ U y hy hw; exact pistes M X H hh N.oboe hX hf hZ h hp hw hy hhp
end
variable {Y t u v:ℝ}{N : March.Captain H j q d v Y A b r B t n χ}(h : Seminar M H p j A χ e v)
open Greenbelt March Next.Foundations

def escort (M:Lotus.Team R) (χ:Chi) (Q:ChartRatio G) (p:Molecule S)(l: ℕ) (T : Tube G S) (W x K a:ℝ) (V:Config G c):=likely fun r:Greenbelt.Reserve S=> M.picture (prism T x χ K V (allot r)) p W a Q l
local notation "U'" => fun V=> escort M χ Q.table p Q.halo T W x o.K o.a V
local notation "l₀" => M.lotus T x χ o.K W o.a Q.table Q.halo


include H N h
lemma debtor (hp:(roster p).flags=∅)(he:0≤e) : LocalOn (H.unionP p) U' ∧ Measurable U' ∧ GaugeInvariant U' ∧
    (fun V=> M.lotus T x χ o.K W o.a Q.table Q.halo V p)=masked (Pressure.temp x) (H.unionP p) U' ∧
    ∀ Y:Config G c,Healthy (Pressure.temp x) (H.unionP p) Y→ Ore Y U' v e j:=by
  let X (r:Greenbelt.Reserve S):=prism T x χ o.K 1 (allot r); let f i V:=M.picture (vary (X i) V) p W o.a Q.table Q.halo
  have h' i:= M.tailSpin (a:=o.a) (X i) p (show Intake P T (X i).x R from H.laws.intake) (show Room P S T (X i).x from H.laws.data.room) (show ShellAccess S G _ _ ((X i).width) o.γ from H.laws.data.access) Q.table_exists Q.buys
  have hf i (V:Config G c): M.bloom (prism T x χ o.K V (allot i)) W o.a Q.table Q.halo p=masked (Pressure.temp x) (H.unionP p) (f i) V∧
      (Healthy (Pressure.temp x) (H.unionP p) V→ Ore V (f i) v e j):= luminos M (prism _ _ _ _ _ _) N h rfl rfl rfl hp he
  let c:= (Fintype.card (Greenbelt.Reserve S):ℝ)
  letI : Nonempty (Forest S.ratio) := Tree.select _ S.patch.odd_side
  have hP:0<c:=by unfold c; positivity
  refine ⟨fun U V h=> congr_arg likely (funext fun i=> (h' i).2.1 U V h),measurable_const.mul (Finset.measurable_fun_sum _ (fun i _=> show Measurable (f i) from (h' i).1)), fun t U=> congr_arg likely (funext fun i=>(h' i).2.2 t U),?_, fun V hU E _ _ _ Z x hx hz=>?_⟩
  · funext V; unfold Team.lotus; simp_rw [fun i=> (hf i V).1]; by_cases hv: Healthy (Pressure.temp x) (H.unionP p) V
    · simp_rw [masked_eq _ _ _ _ hv]; rfl
    simp_rw [masked_ne _ _ _ _ hv]; exact Greenbelt.likely_constant _
  apply ((Brush.spree _ (fun i=> f i ∘ Z) _ zero_le_one (fun i (_:i∈univ)=> (hf i V).2 hU _ Z x hx hz)).smul c⁻¹).climb _ le_rfl
  rw [Real.norm_of_nonneg (inv_nonneg.mpr hP.le),sum_const,nsmul_eq_mul,card_univ, inv_mul_cancel_left₀ (show c≠0 from hP.ne')]

end YM.RemainderComparison.Cascade

