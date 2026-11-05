import YM.FullVolume.E6.Rebuke
/-! E6 Layout steps full volume.Epoch. Keep Records by exact tags.Canvas.Read.F. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Lim
open Function Filter Set Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Org
open Extra.Iteration PhysicalNext.Repeat Greenbelt Match Song Refrain
open Blaze Blaze.March Captain Silica Height Brim Time Supply Input Testing PriceCompiler Opera
open UVNext.CouplingReset Animals Progress.DirectedRecipe Ovens
open Stationary Stationary.Shade Stationary.Beacon Laurent Exterior Bloch
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {P : Teller G} {S : StepData c f} {F : Forest S.ratio}
open Matrix Window Progress.StationaryScenes Green Census Control Flux FullVolume.Shadow
open Gate Frond Vine Mask
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E] {φ: Filter ℕ}{J: Ultrafilter ℕ}{Q:ConnectedActivityE6.Target G P}{W x μ C₀ a b e ℓ v :ℝ}{o:Target.Order G W}
    {Λ: Era G S}{U:ℕ→ E→ Config G c}{Z: Draft F G} {K H:ℕ→ Epoch Λ}{j:ℕ}{p:E}
open FullVolume.Neptune Flux Shield Eider Packets Polar
variable {M:Bank}(I:Depot Q o x μ L C₀ K) (T:Depot Q o x μ L C₀ H){χ: Chi}(R:∀ n, Station M χ (I n) j)(P':∀ n,Station M χ (T n) j)
variable (m:Molecule S) (V:ℕ→ Config G c)
namespace Draft
set_option quotPrecheck false
local notation "D"=>fun n=> prism (K n).tubes x χ o.K (V n) F
local notation "D'"=>fun n=> prism (H n).tubes x χ o.K (V n) F

abbrev mount (F:Forest S.ratio)(G:Gauge)(x:ℝ)(Y:Config G c)(χ: Chi)(k:S.Choices)(p:Molecule S) (b:ℝ): Draft F G:=⟨1,{ (roster p) with flags:= RG.flags (Pressure.temp x) Y},k,χ,x,b⟩
private lemma plantedX {V:ℕ→ Config G c} {χ:Chi}(K:Epoch Λ)(u:Config G c)(k:S.Choices)(v:ℝ)(x:ℝ)(p:Molecule S): (planted (prism K.tubes x χ v u F) p).taggedL k = (mount F G x u χ k p v).paints K u :=rfl
private lemma quiet {p:Molecule S}(K V':Epoch Λ)(k l b) : (areas K.kin K.tubes l b k)=(areas V'.kin V'.tubes l b k):= rfl
lemma preserve {p:Molecule S}(K V':Epoch Λ)(l b) : troupe K.tubes K.kin l b p ↔ troupe V'.tubes V'.kin l b p:=Iff.rfl
private lemma taut {p:Molecule S}(K V':Epoch Λ)(k l):Ac.Spark (areas K.kin K.tubes k l) p ↔ Ac.Spark (areas V'.kin V'.tubes k l) p:=Iff.rfl
lemma honors {p:Molecule S}(K V':Epoch Λ)(l x a)(Y: Config G c)(χ:Chi): standsIn (prism K.tubes x χ a Y F) K.kin l p ↔ standsIn (prism V'.tubes x χ a Y F) V'.kin l p:= Iff.rfl
section estimates
variable {q:ℕ→ Molecule S→ℝ} (h:Clubs M I χ j q)
include I h
open Stained
lemma flies : ∀ n, ‖(I n).spawn χ (V n) m‖ ≤ q n m:=by
    letI : Nonempty (Forest S.ratio):= Tree.select _ S.patch.odd_side
    intro i; have hh (d : Finset (Molecule S)):True:=trivial
    let f(A:Reserve S):= proceedsA (K i).kin (prism (K i).tubes x χ o.K (V i) (allot A)) W o.a Q.halo Q.table m
    have hx {a:Type} [Fintype a] [Nonempty a](g:a→ℝ)(h:∀ i', ‖g i'‖≤q i m): ‖likely g‖≤q i m:=by
          unfold likely; rw [norm_mul,Real.norm_of_nonneg (by positivity : 0≤ (Fintype.card a:ℝ)⁻¹)]
          have hh:= Finset.sum_le_sum (s:=Finset.univ) fun j _=> h j; rw [sum_const,nsmul_eq_mul, card_univ] at hh; exact (mul_le_mul_of_nonneg_left ((norm_sum_le ..).trans hh) (by positivity : 0≤(Fintype.card a:ℝ)⁻¹)).trans_eq (by rw [← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul])
    refine hx f fun i'=>?_; unfold f proceedsA; split; next hi=> exact hx _ fun k=> h.heavy i (allot i') ((planted _ m).taggedL k) rfl rfl rfl rfl m
    rw [norm_zero]; exact h.value.value ..
include R
lemma opine {U:Config G c} (s)(i:(I 0).ThinP) (he:Healthy (Pressure.temp x) ((I 0).smallAt i) U): Ore U (fun V=> leaflet (I s) χ V i) M.v (q s i.val) j:=by
    letI : Nonempty (Forest S.ratio):= Tree.select _ S.patch.odd_side
    intro E _ _ _ V p hi ht; let g(a: Greenbelt.Reserve S)(t:E):= Stained.fringe (prism (K s).tubes x χ o.K (V t) (allot a)) W o.a i.val (K s).kin Q.table Q.halo; apply Captain.avgBrush g
    intro z; let X:=prism (K s).tubes x χ o.K U (allot z)
    have hh: Healthy _ ((I s).unionP i.val) X.V:=he
    refine Brush.shimmy ?_ (show g z=ᶠ[𝓝 p] fun y=> shelter (vary X (V y)) W o.a i.val (K s).kin Q.table Q.halo from Stained.rainbow (X:=X) i.val (R s|>.N.oboe) rfl rfl rfl i.2.2 hh ht hi)
    unfold Shield.shelter; change Brush _ _ _ (fun i'=> if Ac.Spark (I 0).supportP i.val ∧ troupe (K s).tubes (K s).kin Q.halo (radiusB x) i.val then _ else _) _
    split
    · let f(t:S.Choices)(i':E):= bars (podium S G ((I s).unionP i.val) (radiusB x)) ((preps (vary X (V i')) (roster i.val)).taggedL t) i.val (K s).kin Q.table W o.a Q.halo
      apply Captain.avgBrush f; intro k; let Y:= (planted X i.val).taggedL k
      apply (h.steady s (allot z) Y rfl rfl rfl rfl i.val hh E V p ht hi).shimmy (Eventually.of_forall fun y=> (Blaze.spices i.val (I s) X rfl (V y) (V y) (fun _ _ _=>rfl) hh i.2.2 k).symm) -- expects val
    exact Brush.zi EventuallyEq.rfl (h.value.value ..) zero_le_one
end estimates
include I T R P'
variable (h:Sweep K)(he:Sweep H)(hM:Mirror K H)(hJ:(J:Filter ℕ)≤ atTop)
include h he hM hJ
lemma entryA : Glints J (fun n=> (I n).spawn χ (V n) m) (fun n=> (T n).spawn χ (V n) m):=by
    let a(A: Greenbelt.Reserve S)(V)(Y:Epoch Λ):=prism Y.tubes x χ o.K V (allot A); let f(Y:Epoch Λ) (V) (e:Reserve S):=proceedsA Y.kin (a e V Y) W o.a Q.halo Q.table m; change Glints J (fun n=> likely (f (K n) (V n))) (fun n=>likely (f (H n) (V n)))
    refine (Glints.every Finset.univ fun A _=> (?_ : Glints J (fun n=>f (K n) (V n) A) (fun n=>f (H n) (V n) A))).bin (fun x _=> continuousAt_const.mul continuousAt_id); unfold f proceedsA
    have hh n: standsIn (a A (V n) (K n)) (K n).kin Q.halo m ↔ standsIn (a A (V n) (H n)) (H n).kin Q.halo m := Iff.rfl
    have hu : Glints J (fun n=> amountP (K n).kin (a A (V n) (K n)) W o.a Q.halo Q.table m) (fun n=> amountP (H n).kin (a A (V n) (H n)) W o.a Q.halo Q.table m) :=by
        obtain ⟨q,hq⟩:=carded I R (coined _ _ R h).choose_spec
        obtain ⟨B,hB⟩:= hq.value.bound
        let F n (Y:Epoch Λ) (k):= ((planted (a A (V n) Y) m).taggedL k).attains Y.kin Q.table W o.a (own m) Q.halo m
        refine (Glints.every Finset.univ (fun k _=> (?_ : Glints J (fun n=>F n (K n) k) (fun n=> F n (H n) k)))).bin (Q:=fun x=>(Fintype.card S.Choices:ℝ)⁻¹*x) (fun _ _=> continuousAt_const.mul continuousAt_id)
        let Y n:=mount (allot A) G x (V n) χ k m o.K; refine Glints.time ?_ ((behold (V:=V) (Υ:=Y) I T R P' (fun _=>⟨rfl,rfl⟩) (fun _=>rfl) (fun _=>rfl) hM h he m).mono_left hJ)
        exact FullVolume.Shadow.flowers (f:=fun i=>F i (K i) k) (x:=0) (b:=B) (Eventually.of_forall (fun i=> by rw [dist_zero_right]; exact ((hq.heavy i (allot A) ((Y i).paints (K i) (V i)) rfl rfl rfl rfl m).trans (budget_single (hB i) m))))
    exact (switch hu ⟨(0:ℝ),tendsto_const_nhds,tendsto_const_nhds⟩ (fun n=> standsIn (a A (V n) (K n)) (K n).kin Q.halo m)) -- edit
end Draft
end YM.ConnectedActivityE6.Lim
