import YM.AnalyticNext.CONNECTED_LOG_IDENTITY.Prices
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Blush.Sails
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Daisy.Coasts
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Mallow.Tonic

/-!
 # Bake Raw dictionary before PPX. Tilt same.Supports.N and Core at shape printer.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Blush
open Function Filter Lattice RG Wilson Finset MeasureTheory
open Push Push.AbsoluteSums Gas Ovens ConnectedActivityE6 Daisy Daisy.Charity Mallow Lotus
open PowerSeries Extra.Histories Progress.DirectedRecipe Next.Foundations Precision
open Blaze Blaze.March Poll Pond Greenbelt
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G:Gauge}{c f n: Side}
variable {i j:ℕ} {o: Site n}{S:Support n}{B : BudgetPoint}
section caps
lemma ornate {F:Config G n→ℝ} (h:B.Regular S F): B.Regular S (Complex.ofReal ∘ F):=by
  let f:= Complex.ofReal ∘ F
  have he U (hp: Healthy B.threshold S U) : Push.Local.Chart B.order f U := Complex.ofRealCLM.contDiff.contDiffAt.comp _ (h.smooth U hp)
  exact ⟨fun _ _ hx=> congr_arg Complex.ofReal (h.sites _ _ hx), Complex.continuous_ofReal.measurable.comp h.borel,fun _ _=>congr_arg Complex.ofReal (h.symmetry _ _),he,fun _ ht A l h'=> left_has _ h' (he _ ht)⟩
lemma pricingG {F:Config G n→ ℝ}{a:ℝ} (h:B.Regular S F) (hp:B.supBounds o S F a): B.supBounds o S (Complex.ofReal ∘ F) a:= by
  refine ⟨hp.1,fun V hV l hl hu=> ?_⟩
  have he := Local.left_linear Complex.ofRealCLM l (h.smooth V hV) hl
  rw [show leftDerivs (Complex.ofReal ∘ F) l V=((leftDerivs F l V:ℝ):ℂ) from he]; exact (Complex.norm_real _).trans_le (hp.2 V hV l hl hu)

lemma petalscale {F:ℕ→ Config G n→ℂ} (v:ℂ) {A:Activities G n}(hp : Push.Local.ForceFormat B A o F): Push.Local.ForceFormat B A o (v • F):=by
  exact ⟨fun i U h=> hp.forcing i U (right_ne_zero_of_mul h), fun i h=>hp.carried i (fun ht=> h (by change v • F i=0; rw [ht,smul_zero])),fun i k U=>congr_arg (v * ·) (hp.invariant i k U),fun i u w hs ht=> congr_arg (v*·) (hp.supported i u w hs ht),fun i=> (hp.borel i).const_smul v⟩
lemma petalcost {F:ℕ→ Config G n→ℂ} (v:ℂ) {C:ℝ} {A:Activities G n}(h: Push.Local.ForceCost B A F C): Push.Local.ForceCost B A (v • F) (‖v‖*C):= by
  obtain ⟨p,hp,hf⟩:=h; have ht:= norm_nonneg v; refine ⟨(fun i=>‖v‖*p i),?_ ,fun i=>⟨mul_nonneg ht (hf i).1,fun U=>by simp only [Pi.smul_apply,norm_smul]; exact mul_le_mul_of_nonneg_left ((hf i).2 U) ht⟩⟩
  convert budget_scale ht hp using 1; ext i; unfold BudgetPoint.mass; ring
variable {r:ℕ}{X X' : ℕ → Support n} (v:ℂ) (R : Rep G n) (F : ℕ→ Config G n→ℂ) (U : Config G n)

-- bridge.PackedBook fully enumerated (issue shape comparator etc global).

lemma breakT (t:ℝ)(X : Support n)(f g : Config G n → ℂ)(V:Config G n): masked t X (f+g) V= masked t X f V + masked t X g V:= by by_cases h:Healthy t X V <;> simp [h]
lemma liquid (t:ℝ)(X : Support n)(f : Config G n→ℝ) (V:Config G n): masked t X (Complex.ofReal ∘ f) V=(masked t X f V:ℝ):=by by_cases h:Healthy t X V<;> simp [h]
end caps

open Pressure Push.SectorMeasure Greenbelt Refrain
variable {S:StepData c f}{T: Tube G S}{L:Side}{P:Teller G} {Q: ConnectedActivityE6.Target G P}{W x μ C : ℝ}{o':Target.Order G W}{R:RG.Rep G f}
variable (H:Cash W x μ L Q o' C T R) (r : Cloud R) (o : Site c)
local notation "hd"=> r.live
local notation "hd'"=> r.pale
local notation "χ"=> Chi.canonical
-- same.Support literal.Report. use marker index.Price matrix later.Sigma
lemma arches (i : H.fragrances): Charity.locus (hd) H o i= Charity.locus (hd') H o i:= by unfold locus speaks; rw [r.together]
lemma arches' (i : H.fragrances): prince r.live H i ↔ prince r.pale H i:= by unfold prince; rw [r.together]
lemma jewels : jewelDebt (hd) Q L x=jewelDebt (hd') Q L x:=by unfold jewelDebt; rw [r.rates,r.turnout]
variable (K R' : ℝ → Code G c)
variable (v: ℂ)

-- witness printer pads supports on NEVER-realized fragrances.Natural via stuff. costs.
def enter : H.fragrances ↪ ℕ:=
  let _ := Classical.choice (nonempty_encodable H.fragrances); ⟨Encodable.encode,Encodable.encode_injective⟩
def scope (i:ℕ):Support c:= Function.extend (enter H) (locus r.live H o) (fun _=>{o}) i
def pane (p:H.fragrances): Config G c→ℂ:=v • (Complex.ofReal ∘ matin r.live H p χ + Complex.I • (Complex.ofReal ∘ matin r.pale H p χ))
local notation "s" => scope H r o
def fields := stuff (enter H) (pane H r v)
def plaque:= v • (nectar K+Complex.I • nectar R')
variable (F : YM.Labels.Frame G j) -- edit

def screen : Push.Local.Raw F c:=⟨0,fields H r v,plaque K R' v⟩ -- R' and K order
section Tags
variable {q t u Y A b a k' t' B' C':ℝ}{k ℓ :ℕ} (N : Captain H k q t u Y A b a B' C' ℓ Chi.canonical) (h: Herd H N.conduit A B' ℓ)
variable {y:ℝ} (ho:o∈r.live.crest.image S.ratio.parent)(hx: B.threshold=Pressure.temp x)(hp : B.order≤k) 
include h ho hx hp
lemma anatomy {R2 : Rep G c}(he:R2.p=B) (h1: Push.Local.ForceFormat B R2.activities o (nectar K)) (h2: Push.Local.ForceFormat B R2.activities o (nectar R')) : (Blush.screen H r K R' v F).Format o (scope H r o) R2:=by
  set M:=v • (nectar K+Complex.I • nectar R'); have hz : Push.Local.ForceFormat R2.p R2.activities o M:= he.symm ▸ petalscale v (h1.add (petalscale _ h2))
  suffices hf : ∀ i,o∈(scope H r o i) ∧ B.Regular (scope H r o i) (fields H r v i) from ⟨fun i=> (hf i).1,fun i=> (he.symm ▸ (hf i).2 : R2.p.Regular _ (fields H r v i)),hz⟩
  intro i; by_cases hq:i∈ Set.range (enter H); swap; · unfold fields scope; rw [Function.extend_apply' _ _ _ hq,blank _ _ hq]; exact ⟨Finset.mem_singleton_self _, (regular0 _ _ o).1⟩
  obtain ⟨i,rfl⟩:= hq; unfold scope fields; rw [(enter H).injective.extend_apply, stuffed]; refine ⟨seatY r.live H o ho _, regular_smul _ (regular_add (ornate (scops r.live H N h B ho hx hp i)) ?_)⟩
  rw [arches]; exact regular_smul _ (ornate (scops r.pale H N h B (r.turnout ▸ ho : o∈r.pale.crest.image S.ratio.parent) hx hp i))
end Tags
end YM.PhysicalNext.Repeat.Blush
