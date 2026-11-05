import YM.AnalyticBridge.LOCAL_GAUSSIAN_MULTIPLIER.Draped
import YM.AnalyticBridge.LOCAL_GAUSSIAN_MULTIPLIER.Noise
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Heir.Gates
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Psalm.Hush

/-! # Example physical complement & guarded E companion alphabet for
*pricing*, keeping exact tests and authentic POV on the sector change.
NOT deciding eligibility/overlap/compulsory assignment (nor legitimating
an altered allocation by dropping guards). Complete ordering/exposure
record, support and agreements when putting these rewrites in Programme
etc required separately. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.JointLoad.Psalm
open Function Filter Set Lattice Wilson RG Tree Pressure Precision Next Next.SectorChange Wisps Bid
   Push.SectorMeasure WardBin.Lies Planned.AtomRegular.Foliage AnalyticBridge.LocalGaussianLaws
   AnalyticBridge.LocalGaussian Heir
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical ContDiff
variable {G : Gauge} {c f : Side} {S : StepData c f} {F : Forest S.ratio} {A : Stores S} {k : S.Choices} {d : Desk G S}
    {I : Type} [Fintype I] {X X' : Support f} {Y : Support c} {n : ℕ} {Pt : Teller G} {C : Libretto G n} {D : Record} {Bt : Baton G}
    {r : ℝ} {V : Config G c}

inductive Pitch (S : StepData c f) (I : Type) where
  | door (i : I)
  | fine (p : Cell f)
  | frame (o : Site c)
  | noise (j : Bond c)
  | connector (j : Bond c)
  | void (x : Site f)
  | inherit (l : ℕ)
namespace Pitch
variable (a : Museum F d.betaHat A X Y I) (p : Pitch S I)

def ground : Set (Site f) := match p with
  | .door _ | .inherit _ => ∅ -- guard at door: singleton, E: full Museum, not accessing this Set
  | .fine j => touched j
  | .frame o => frameUses S o
  | .connector j | .noise j => predictorUses S j
  | .void x => inspected {x}

def carriers : Finset I := match p with
  | .door i => {i}
  | .inherit _ => Finset.univ
  | p => Finset.univ.filter (fun i => Needs p.ground (a.address i))

def Eligibility (_a : Museum F d.betaHat A X Y I) : Prop := match p with
  | .door _ => True
  | .inherit l => (d.labels.reg l).support ⊆ X
  | .fine j => Tests X j
  | .frame o => frameUses S o ⊆ inspected X
  | .connector j | .noise j => predictorUses S j ⊆ inspected X
  | .void x => x∈X

variable (d) in
-- ψ profile beyond every broad γ, per *all possible regular* stencil hard arguments
-- even if already read or on a zero-likelihood packet. Consume under same chart radius.
def openedPatch (s : Finset I) (y : I → G.Color) := ∏ i∈s,broad d.broadCut (2*d.radius) (y i)

def patched := openedPatch d (p.carriers a)

abbrev muffler (d : Desk G S) (I : Type) [Fintype I] (D : Record) := Heir.guard d.profile G I d.g (cap D d)
abbrev stripped (d : Desk G S) (U : Config G f) (ψ : ℝ) (l : ℕ) := Real.exp (-d.labels.regularOccurrence d.input.p l U * ψ)-1
abbrev unmasked (d : Desk G S) (D : Record) (z : Prices G I) (U : Config G f) (ψ : ℝ) (l : ℕ) := Real.exp (-(muffler d I D z * d.labels.E l U)*ψ)-1

variable (k) (b : Finset ℕ) (D)
/-- Operands requiring a Gaussian trigger. No scalar or combined row assigned here.
All signs as in the exponent; the remaining principal choice at an E address
has `unmasked`, POSITIVE sign as a Mayer choice (minus applies at later log).
The Γ scale uses the genuine centered Z (also at HELD U in a differentiated
term), not the poured displacement or an independent sector. Caller MUST
back up every read with full stencils, not ignoring suppressed arguments.
-/
def stopped (V : Config G c) (z : Prices G I) (U : Config G f) (y : I → G.Color) := let h := spectacle d A F k; let ψ := p.patched a y
  match p with
  | .door i => broad d.broadCut d.radius (y i)-1
  | .fine j => (h.fineBit j U-1)*ψ
  | .frame o => (h.frameBit o U-1)*ψ
  | .noise j => (h.noiseBit j V U-1)*ψ
  | .connector j => (h.connectorBit j U-1)*ψ
  | .void x => (d.qVoid b x U-1)*ψ
  | .inherit l => stripped d U ψ l-unmasked d D z U ψ l

def continued (U : Config G c → Config G f) (w : Config G c → Prices G I) (W : Config G c) :=
   p.stopped k D a b W (w W) (field k a U w W) (liftU k a U w W)

abbrev Ratings := (spectacle d A F k).Visual
abbrev gaussRead (y : Ratings (A:=A) (F:=F) (k:=k)) := y.2 ∘ a.colorSeat G
abbrev actualRead (W : Config G c) (y : Ratings (k:=k)) := fun i => displaced ((spectacle d A F k).m W y.1) d.g y.2 (a.seat i)
def actual (V : Config G c) (y : Ratings (k:=k)) := p.stopped k D a b V (gaussRead k a y) ((spectacle d A F k).hard V y) (actualRead k a V y)





lemma inspect_subset {X X' : Support f} (h : X'⊆X) : inspected X'⊆ inspected X := by
  intro i hi; obtain hi|hi := Finset.mem_union.mp hi
  · exact Finset.mem_union_left _ (h hi)
  obtain ⟨p,-,hp⟩ := Finset.mem_biUnion.mp hi
  split at hp; simp at hp
  next hd => obtain ⟨x,hx,hp'⟩ := Finset.not_disjoint_iff.mp hd; exact (show Tests X p from ⟨x,h hx,hp'⟩).retain hp

def Allowed (d : Desk G S) (p : Pitch S I) := ∀ l, p=.inherit l → LocalOn (d.labels.reg l).support (d.labels.E l)

variable {p a k D} (he : p.Eligibility a) (hs : p.Allowed d) (hT : Sounded Pt C D Bt r d) (hV : Healthy d.out.threshold Y V)
include he hs hT hV
/- Exact pointwise at this V, also if p is interpreted at a true hard
configuration on that SAME system but local kernel comparison at only
partially tested output flags. Other expressions and changes/completions
NOT automatically backs of this occurrence. -/
lemma holds (y : Ratings (k:=k)) (U : Config G c → Config G f) (w : Config G c → Prices G I) (hw : gaussRead k a y=w V) :
    p.actual k D a b V y = p.continued k D a b U w V := by
  have hh := hT.rehearsed.temp_eq ▸ hV; have hT' := hT.bulletin.priced; have hS : S.patch.Branches S.kernel G := hT'.knobs.symm ▸ hT'.kernel
  let s := spectacle d A F k; let Z := s.hard V y; let Z' := field k a U w V
  let f₀ : Frozen A d.betaHat F → Bond _ := fun i => i.val.val; have hf₀ : Injective f₀ := fun _ _ h => Subtype.ext (Subtype.ext h)
  let Z₀ := Function.extend f₀ y.1 1; have hU : y.1=Folio.leaf A F d.betaHat Z₀ := (funext fun i => hf₀.extend_apply y.1 1 i).symm
  have hh' : Agrees (Y:Set _) V V := fun _ _ _ => rfl
  have hj : Agrees (inspected X) Z' Z := by
    have hv := a.variations (k:=k) (d:=d.radius) (q:=d.broadCut) (u:=d.g) hT.bulletin hh' (U V) Z₀ (w V)
    intro i hi hj; apply (hv i hi hj).trans
    unfold Z Spot.hard; rw [← hw]; nth_rw 1 [hU]; rw [show s.m V y.1 = _ from congr_arg (s.m V) hU]; exact a.masked_reads hT.bulletin hh Z₀ y.2 i hi hj
  have hl : liftU k a U w V=actualRead k a V y := by
    funext i; unfold liftU actualRead; rw [credited a,← hw]; unfold vocal; rw [a.seat_mean hT.bulletin hh' i (U V) Z₀,a.m_actual hT.bulletin hh Z₀,← hU]; rfl
  have hx (E : Set (Site f)) (hE : E ⊆ inspected X) : Agrees E Z' Z := fun e hi hh => hj e (hE hi) (hE hh)
  unfold continued actual; rw [hl,hw]
  unfold stopped; cases p with
  | door i => rfl
  | fine j => exact congr_arg (fun t => ((if j∈A.costs then 1-d.profile.innerShare (fiery G d.betaHat S.patch.L/4) t else d.profile.innerShare (fiery G d.betaHat S.patch.L/4) t)-1)*_) (congr_arg G.chord (travel_local _ _ Z Z' (fun i h h' => (hj i (Tests.retain he (List.mem_toFinset.mpr h)) (Tests.retain he (List.mem_toFinset.mpr h'))).symm)))
  | frame o => exact congr_arg (fun t => (t-1)*_) ((knows_site s _ hS Z' Z (hx _ he)).symm)
  | noise j => exact congr_arg (fun t => (t-1)*_) ((Notice.forward_agrees (u:=s) j hS (hx _ he) V).symm)
  | connector j => exact congr_arg (fun t => (t-1)*_) ((Notice.knows_connector s j hS Z' Z (hx _ he)).symm)
  | void x =>
    have hf := flags_agree d.input.p.threshold _ _ {x} (hx _ (inspect_subset (Finset.singleton_subset_iff.mpr he)))
    have hi (g : Config G f) : x∈flags d.input.p.threshold g ↔ x∈({x}:Finset _)∩flags d.input.p.threshold g := by simp
    dsimp only; unfold Desk.qVoid; change ((if _ ∨ x ∉ flags _ Z then _ else _) - _) * _ = ((if _ ∨ x ∉ flags _ Z' then _ else _) - _) * _
    simp only [hi Z, hi Z', hf]
  | inherit l =>
    have hf : d.labels.E l Z'=d.labels.E l Z := hs l rfl _ _ (hx _ (Finset.Subset.trans he Finset.subset_union_left))
    have hH : Healthy d.input.p.threshold (d.labels.reg l).support Z ↔ Healthy d.input.p.threshold (d.labels.reg l).support Z' := by simp only [Healthy,Finset.disjoint_iff_inter_eq_empty, flags_agree d.input.p.threshold Z' Z _ (hx _ (inspect_subset he))]
    have hk : d.labels.regularOccurrence d.input.p l Z=d.labels.regularOccurrence d.input.p l Z' := by
      unfold Activities.regularOccurrence; by_cases hi : Healthy d.input.p.threshold (d.labels.reg l).support Z
      · rw [masked_eq _ _ _ _ hi,masked_eq _ _ _ _ (hH.mp hi),hf]
      rw [masked_ne _ _ _ _ hi, masked_ne _ _ _ _ (mt hH.mpr hi)]
    dsimp only; unfold stripped unmasked; change (Real.exp (-d.labels.regularOccurrence _ l Z * _) - 1) - (Real.exp (-(_ * d.labels.E l Z)*_) - 1)= (Real.exp (-d.labels.regularOccurrence _ l Z' * _) - 1) - (Real.exp (-(_*d.labels.E l Z')*_) - 1)
    rw [hf,hk]
end Pitch
end YM.PhysicalNext.JointLoad.Psalm
