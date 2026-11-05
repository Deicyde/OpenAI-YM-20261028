import YM.Next.RANK.PaperGate

/-!
# Using the endpoint formal recursion

End comparison is for the true free comparator. Use right-lower subset estimates
before using log: any missing singleton cost would enter here. This works even
though labels not *equal* to limits at every p. Everything is compared to the
free moment polynomial at the same stage on the right physical lifts. -/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Atlas
open Lattice Wilson RG Station Labels Price Prayer Glimmer Rise Perch  Beamer Cells Common Normal Filter Marker Glyph Exponential Read Configuration Particle
open scoped Topology BigOperators Classical ContDiff

variable {G : Gauge} {C : Family G} {d k N p n : ℕ} (v : Fin n→ C.label d)

def joint (t : Fin n → C.label d) : Fin n→ (standard C).Tag := fun i => ⟨d,(standard C).project d (t i)⟩
lemma stages (v : Fin n → C.label d) (x : Points n) (h : x ∈ conf _) T :
    (Read.maxProfile C x (joint v)).part T=Maxwell.Wick.moment G (Read.portion T x) (fun i => Maxwell.observable G d ((C.labels.level d).coords.symm (v ((Read.project T) i).val))) := by
  let X:= standard C
  let w:= fun i => (Read.project T i).val
  let t (i) : (Maxwell.standard C.labels).Token := ⟨d,v i⟩
  have ht := X.at_project X (Maxwell.table_regular _).toSymmetric (fun _ => le_rfl) (Read.portion_free T x h) (fun i => t (w i))
  exact ht

-- pins are gathered ON a real coarse-lattice endpoint input. It fits inside near-test ranges.
section
variable (P : Levels G) (X : AtlasData G P.S p)
variable {w : Fin n → Cover} {l : ℕ} {hi : l≤ k}

-- gauge amplitude permitted at l. `Bell` expects every such Y (and closure can be required on full torus through wrapping), reuse same m for all local subsets.
def Wind (g : Chamber G P.S l p → ℝ) (B : ℝ) :=
    (∀ i, ‖g i‖≤B) ∧ shutter (fun i : Address G => g (body 0 i))

def μre (P : Schedule) (X : AtlasData G P p) (w : Fin n → Cover) (hi : l≤k) (m : Chamber G P l p→ℂ) : Fin n→ Horizon G := fun i a => (noise X w hi m (i,a)).re

def Γre (P : Schedule) (X : AtlasData G P p) (w : Fin n → Cover) (hi : l≤k) : Fin n→Fin n→ Bridge G := fun i j a b =>
    ((Qmarks X w hi).cov (i,a) (j,b)).re

lemma Γs (w : Fin n → Cover) (hi : l≤k) : ∀ i j a b, Γre P.S X w hi i j a b=Γre P.S X w hi j i b a := by
  intro i j a b; unfold Γre; rw [Normal.Symmetric.symm]

/-- Finite miscompare gates on kernels. Supports are true native l/k levels. At A k root require universal over Wind (on each pulled orientation inquiry). -/
structure Bell {b : ℝ} (d : ℕ) {x : Points n} (deg : ℕ) (hx : Fit P b k x) : Prop where
  validQ i j :
    let Q := Qmarks X (Station.choose P b k x) (before P b k)
    ((Q.cov i j).re:ℂ)=Q.cov i j
  validM (m : Chamber G P.S (middle P b k) p→ℝ) : Wind P m (fraction n deg (clim P k)) → ∀ i,
    let u:= noise X (Station.choose P b k x) (before P b k) (fun x => (m x:ℂ)) i
    (u.re:ℂ)=u
  verdict (m : Chamber G P.S (middle P b k) p → ℝ) (h : Wind P m (fraction n deg (clim P k))) :
    let f := Station.choose P b k x
    Reads d (Ship.fitting hx) (mag P b k) (Γre P.S X f (before P b k))
      (μre P.S X f (before P b k) (fun x => (m x:ℂ))) (lengthW (clim P k)) (fraction n deg (clim P k)) (bill (-3) (clim P k))
end

variable {Y : AtlasData G C.S p}

variable {x : Points n} {b : ℝ} (g : Fit C.path.levels b k x) (degree : ℕ)
variable {Z : Heater C k d} {T : C.label d→ₗ[ℂ] C.label d}

theorem sizes (hN : k≤N) (D : Heating C k N p d degree Z T) (h : Bell C.path.levels Y d degree g)
    (m : Chamber G C.S (middle C.path.levels b k) p→ℝ) (hm : Wind C.path.levels m (fraction n degree (clim C.path.levels k)))
    (H : passing v k degree b) (u : Fin n → C.label d) (hU : ∀ i,Price.Solves C (mag C.path.levels b k) d k N p T (v i) (u i))
    (hs :
      let s:=clim C.path.levels k
      Meridian d (Ship.fitting g) (G:=G) (fraction n degree s) (fraction n degree s) (bill (-3) s) (bill (fuel degree n) s)
        (bill (-2) s) (Station.mag C.path.levels b k) (lengthW s)) (q : Glyph.modes (Fin n)) :
    let A:= C.path.levels
    let w:= Station.choose A b k x
    ‖(Answer Y w (before A b k) (fun i => Z (u i)) (fun x => (m x:ℂ))).part q-(Read.maxProfile C (Station.tested A b k x) (joint v)).part q‖ ≤ bill (-3/2) (clim A k) := by
  intro A w
  obtain ⟨U,hB,hc,hF,h₁⟩ := H N p hN Z T D u hU
  let M₀ := lengthW (clim A k)
  let l := Station.middle A b k
  let g₀ := (Subtype.val : trimV M₀ G → _)
  let Γ:= Γre A.S Y w (before A b k)
  let μ:= μre A.S Y w (before A b k) (fun x => (m x:ℂ))
  let K:= Γs A Y w (before A b k)
  let r:= mag A b k
  let Q := Qmarks Y w (before A b k); let U' := noise Y w (before A b k) (fun x => (m x:ℂ))
  let f := fun i : Fin n × trimV M₀ G => (i.1,i.2.val)
  let S := primary d g₀ r Γ K
  let V := Beamer.seen d g₀ r μ
  let L := Normal.perSlot (fun _ : Fin n => features d g₀ r)
  have hT : Normal.scope (fun i => Finsupp.single (f i) 1) Q=Normal.scope L S := by
    have ht : Normal.scope L S=prize g₀ Γ K := shaped d g₀ r Γ K (zero_lt_one.trans_le h₁.radius)
    rw [ht]; apply Normal.Symmetric.ext; funext i j; rw [Normal.match_name f]; exact (h.validQ ..).symm
  have hv : U' ∘ f= Normal.reads L V := by
    funext i; rw [show Normal.reads L V i= _ from scanned d g₀ r μ i (zero_lt_one.trans_le h₁.radius)]
    exact (h.validM m hm _).symm
  let X' := Prayer.Reads d (Ship.fitting g) r Γ μ
  have hh := Prayer.resolution d (Ship.fitting g) r _ hs g₀ (fun i => (tracing ..).1 i.property) Γ μ K (h.verdict m hm)
  rw [Answer_part, stages _ _ (Ship.fitting g),← hF]
  exact Particle.accuracy h₁ (Ship.fitting g) S V q _ _ hT hv (hB ▸ hh.1) (hB ▸ hc ▸ hh.2)
end YM.Next.Rank.Atlas
