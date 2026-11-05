import YM.Next.ROTATIONS.Switch
import YM.Next.SCHEDULE.Markets
import YM.PhysicalNext.ACTUAL_SECTOR_FACTOR_DICTIONARY.Print
import YM.PhysicalNext.ACTUAL_SECTOR_FACTOR_DICTIONARY.Route

/-! Index the *same* local variables of Sharp.Ribbon and of Viewport
(where H are hard U arguments but still regular Z positions in the
intact change-of-variables). -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Dictionary
open Function Filter Set Lattice RG Wilson Pressure Pressure.Tube Pressure.Stores Tree Precision Exterior MeasureTheory Matrix
open Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Push.SectorMeasure Push.SectorMeasure.Oriented
open AnalyticBridge.Annulus AnalyticBridge.Annulus.Map
open AnalyticBridge.RelativeLogdet
open AnalyticBridge.Sharp AnalyticBridge.LocalGaussian
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff

namespace Route.Badge
open Print Geo Completion Wires
variable {G : Gauge} {c f : Side} {S : StepData c f} {x : ℝ} {F : Forest S.ratio} {A O : Stores S} {X : Support c}

section crop
variable (b : Badge S x X)

def embroider (t : (b.ribbon F O).Page G) : Refs G f :=
  let r := b.ribbon F O
  ((fun e=> if ht : e∉F.trunks then if h : (⟨e,ht⟩:F.Free)∈r.frost then t.1 ⟨⟨e,ht⟩,h⟩ else 1 else 1),
    fun e=> if ht : e∉F.trunks then if h : (⟨e,ht⟩:F.Free)∈r.breeze then tape t.2 ⟨⟨e,ht⟩,h⟩ else 0 else 0)

theorem embroider_meas : Measurable (b.embroider (F:=F) (O:=O) (G:=G)) := by
  unfold embroider; dsimp only; refine Measurable.prodMk (measurable_pi_lambda _ fun e=> ?_) (measurable_pi_lambda _ fun e=>?_)
  · split
    · split
      next hv hv' =>
        let e' : (b.ribbon F O).live := ⟨⟨e,hv⟩,hv'⟩
        exact (measurable_pi_apply e').comp measurable_fst
      exact measurable_const
    exact measurable_const
  split
  · split
    next hv hv' =>
      let e' : ↥(b.ribbon F O).breeze := ⟨⟨e,hv⟩,hv'⟩
      have hi := (tape (G:=G) (ι:=↥(b.ribbon F O).breeze)).measurable
      exact (measurable_pi_apply e').comp (hi.comp measurable_snd)
    exact measurable_const
  exact measurable_const

theorem identical (h : (b.ribbon F O).Placed x A) (p : Room G x F A)
    (he : ∀ e : F.Free, S.ratio.parent e.val.1 ∈ X → (chill O x F e ↔ chill A x F e)) :
    Same S X b.near (backdrop x A F p) (b.embroider (Ribbon.look h p)) := by
  let r := b.ribbon F O
  constructor
  · intro i h1 h2
    unfold backdrop embroider; dsimp only
    split
    next hv =>
      let e : F.Free := ⟨i,hv⟩
      have hh : e ∈ r.frost ↔ chill A x F e := by
        unfold r Badge.ribbon dreams; simp only [Finset.mem_filter,Finset.mem_univ,true_and,e,h1,h2,and_self,and_true]; exact he e h1
      by_cases hz : e∈r.frost
      · rw [dif_pos (hh.mp hz),dif_pos hz]; rfl
      rw [dif_neg hz, dif_neg (mt hh.mpr hz)]
    rfl
  intro i h1 h2
  unfold backdrop embroider fresh; dsimp only
  split
  next hv =>
    let e : F.Free := ⟨i,hv⟩
    have hh : e∈r.breeze ↔ ¬chill A x F e := by
      unfold r Badge.ribbon Badge.tests
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,e,h1,h2,and_self,and_true]; exact not_congr (he e (b.contained_site h1))
    by_cases hz : e∈r.breeze
    · rw [dif_pos hz,dif_pos (hh.mp hz)]; rfl
    rw [dif_neg hz,dif_neg (mt hh.mpr hz)]
  rfl
end crop

section lens
variable (d : AnalyticBridge.LocalGaussian.Desk G S) (F : Forest S.ratio) (H : Next.SectorChange.Gaussian.Table (Key F G))
  (A : Stores S) (k : S.Choices)

/-- The retained step Spot. Takes the normalization reference even if it is
written at another full tag (see `Native.shared`). -/
def camera : Spot d where
  A := A
  F := F
  k := k
  H := H
  C := fun V=> fog A F d.tube d.betaHat V k
  m := fun V=> meanLog A F d.tube d.betaHat V k d.broadCut d.radius
  stencils := shots S d.betaHat

variable (b : Badge S d.betaHat X)

abbrev Smoke := ↥(b.ribbon F A).breeze
abbrev Hues := {i : b.Smoke d F A // i.val.val∈b.held}
abbrev Cool := {i : b.Smoke d F A // i.val.val∉b.held}
abbrev Test := (b.ribbon F A).live

def tone : (b.Hues d F A ⊕ b.Cool d F A) ≃ b.Smoke d F A where
  toFun := Sum.elim Subtype.val Subtype.val
  invFun i := if h : i.val.val ∈ b.held then Sum.inl ⟨i,h⟩ else Sum.inr ⟨i,h⟩
  left_inv := by rintro (i|i) <;> simp [i.property]
  right_inv := by intro i; dsimp only; split <;> rfl

private def stove : b.Smoke d F A ↪ Active A d.betaHat F :=
  ⟨fun i=>⟨i.val,(b.here F A).breeze i.val i.property⟩,fun i j h=>Subtype.ext (congr_arg (fun z : Active A d.betaHat F => z.val) h)⟩
private def chest := Ribbon.slide (b.here F A)

private lemma both (e : Bond f) (h : S.ratio.parent e.1∈X ∧ S.ratio.parent (e.1+Lattice.step e.2)∈X) :
    Next.SectorChange.points S e ⊆ X := by
  intro y hy
  rcases Set.mem_insert_iff.mp hy with h'|h'; exact (h'.symm ▸ h.1)
  rw [Set.mem_singleton_iff] at h'; exact (h'.symm ▸ h.2)

def lens : Viewport (camera d F H A k) X (b.Hues d F A) (b.Cool d F A) (b.Test d F A) where
  read := (b.tone d F A).toEmbedding.trans (b.stove d F A)
  held := b.chest d F A
  activePos i := both _ ((b.ribbon F A).wind _ (b.tone d F A i).property)
  heldPos i := both _ ((b.ribbon F A).ice _ i.property)

abbrev Person := Display G (b.Hues d F A) (b.Cool d F A) (b.Test d F A)

def blot (p : b.Person d F A) : (b.ribbon F A).Page G :=
  (p.1,fun j=>p.2 ((b.tone d F A).symm j.1,j.2))

def embed (p : b.Person d F A) : Refs G f := b.embroider (b.blot d F A p)

lemma blot_meas : Measurable (b.blot d F A) := by
  unfold blot
  exact measurable_fst.prodMk (measurable_pi_lambda _ fun i=> (measurable_pi_apply _).comp measurable_snd)
lemma embed_meas : Measurable (b.embed d F A) := (b.embroider_meas).comp (b.blot_meas d F A)

lemma color (p : Spot.Visual (camera d F H A k)) :
    b.blot d F A ((b.lens d F H A k).info p)=Ribbon.look (b.here F A) p := by
  refine Prod.ext rfl ?_
  funext j
  have hv := (b.tone d F A).apply_symm_apply j.1
  change p.2 (b.stove d F A ((b.tone d F A) ((b.tone d F A).symm j.1)),j.2)=p.2 (Ribbon.lighten (b.here F A) j)
  rw [hv]; rfl

lemma snap (p : Spot.Visual (camera d F H A k)) :
    Same S X b.near (backdrop d.betaHat A F p) (b.embed d F A ((b.lens d F H A k).info p)) := by
  unfold embed; rw [color]; exact b.identical _ _ (fun e _=>Iff.rfl)
end lens
end Route.Badge
end YM.PhysicalNext.Dictionary
