import YM.ProjectorNext.PROJECTOR_CALIBRATION.Tails
import YM.ProjectorNext.PROJECTOR_CALIBRATION.Triangle
import YM.Push.CUTOFF_PROJECTORS.Stencil

/-!
# Installation on SAME Campaign

Operational hypothesis only about `.weights` and addresses of `.chain` at N
for exact TopTest, then the same `.Compares` as before. No tested accuracy,
upper rank, or bounds implicit in the hypothesis. Provide also d,N,p scopes
and variants even on mesh-before-period and before extracting. Oriented is
NOT included in these sufficient conditions; further transfer promises such
as Oriented are still needed separately for other outputs than Separation.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ProjectorNext.Calibration
open Lattice Wilson RG Source Source.Drops Extraction Function Filter Labels Work Tensor Next.Foundations Push.CutoffProjectors
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff
variable {G : Gauge} {C : Family G} {d : ℕ} (A : Campaign C) (M : Machine C.params d)

/-- The initialization requirements needed so far regarding actual packet data. No
promises outside the use tails. Local initialization only needed in `chain` at N,
not through intermediate transfer. When using even only separated continuum lands,
remember to pay Top on the *same path and slices* as the reconstruction machinery
summons. -/
structure Wears (N p : ℕ) : Prop where
  stamps : M.lined (A.packet d N p)
  shards (i) : let F := C.labels.level d
               let Q := (A.packet d N p).chain N (parameters F i)
               ∃ s : Finset ℕ, (∀ j ∉ s, Q.regular j=0) ∧ ∀ j∈s, Nonwrapping (Q.support j) 0

/-- Discharge Bill with finite initialization. Even uniform in p (authentic
ComesFrom, weights and support promises asked where using Bill). -/
theorem banked (hG : G.Simple) (I : Finset (Lens G d)) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ p, A.start d p ≤ N → Wears A M N p →
      (A.packet d N p).Bill (M.trophy (C.labels.level d)) I ε := by
  let F:= C.labels.level d
  filter_upwards [M.funded hG A.cutoff I ε hε] with N h p hN hh
  refine ⟨fun i => ?_, h p _ hh.stamps⟩
  obtain ⟨s,hs,ht⟩ := hh.shards i
  exact Packet.top_of_finite (A.uses _ _ _ hN) A.cutoff _ s hs ht

/-- Expose also the period-uniform conditional countdown. -/
theorem earned (hG : G.Simple) :
    ∃ c> (0 : ℝ), ∀ᶠ N : ℕ in atTop, ∀ p, A.start d p ≤ N → Wears A M N p →
      ∀ W : Bid.Worth, Bid.Bank W C.path.levels → Bid.roomCost C.path.levels W →
      (A.packet d N p).Compares W → (A.packet d N p).Separation c := by
  obtain ⟨I,ε,c,h1,h2,h3⟩ := spectral_bank d (M.trophy (C.labels.level d)) (M.certified _)
  refine ⟨c,h2,?_⟩
  filter_upwards [banked A M hG I ε h1] with N h p he hh W hb hr ht
  exact h3 _ _ _ (h _ he hh) A.cutoff W hb hr ht

/-- One positive singular margin per d, SAME even for uses every finite period
and uses just on the ordered tails. On the actual projector's matrix measured
in family chart ℓ²: i.e., on `factory(d,N,p).terminal.symm` AFTER equation
`reference`, applied to the *equation* argument in `equationSpace F` (no
primary cost at extraction reference silently substituted). -/
theorem margin (hG : G.Simple) : ∃ c> (0 : ℝ), ∀ (W : Bid.Worth), Bid.Bank W C.path.levels → Bid.roomCost C.path.levels W →
    ∀ f : Extraction.Order,
      (f.late (fun N p => Wears A M N p ∧ (A.packet d N p).Compares W) → f.late (fun N p => (A.packet d N p).Separation c)) ∧
      ∀ p, (∀ᶠ j : ℕ in atTop,Wears A M (f.mesh j) p ∧ (A.packet d (f.mesh j) p).Compares W) →
        (∀ᶠ j : ℕ in atTop,(A.packet d (f.mesh j) p).Separation c) := by
  obtain ⟨c,hc,he⟩ := earned A M hG
  refine ⟨c,hc,fun W hb hr f => ?_⟩
  have hx p : ∀ᶠ j : ℕ in atTop, Wears A M (f.mesh j) p ∧ (A.packet d (f.mesh j) p).Compares W → (A.packet d (f.mesh j) p).Separation c := by
    filter_upwards [f.mesh.cofinal.eventually he, f.mesh.cofinal.eventually (eventually_ge_atTop (A.start d p))] with j h hj hh
    exact h p hj hh.1 W hb hr hh.2
  exact ⟨fun h => h.mono fun _ hu => (hu.and (hx _)).mono (fun _ hk => hk.2 hk.1),fun p h => (h.and (hx _)).mono (fun _ hk => hk.2 hk.1)⟩





/-- Truly zero input equation rank has no obstruction (Bill or Separation).
Works even if *no* thresholds serve fitted data; no min over empty set.
Thus users at very low orders need not commission any Machine hypotheses
(e.g., if `I` is empty in their scheme because no equations used). -/
theorem empty_space {d N p : ℕ} (E : Packet C d N p) (h : Module.finrank ℂ (Maxwell.equationIdeal G d)=0)
    (T : Model (C.labels.level d)) (I : Finset (Lens G d)) (ε : ℝ) :
    E.Bill T I ε ∧ E.Separation 1 := by
  let F:=C.labels.level d
  have hz : Module.finrank ℂ (equationSpace F) = 0 := (equation_dim F).trans h
  have hZ (i : Fin (Module.finrank ℂ (equationSpace F))) : False := by have := i.isLt; omega
  haveI : Subsingleton (equationSpace F) := (Module.finrank_zero_iff ..).1 hz
  exact ⟨⟨fun i => False.elim (hZ i),fun i => False.elim (hZ i)⟩,one_pos,fun i => by
    have he : i=0 := Subsingleton.elim ..; simp [he]⟩
end YM.ProjectorNext.Calibration
