import YM.Next.RANK.Gust
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Edition
open Function Filter RG Thirst Lattice Wilson MeasureTheory Marker Value Perch Vac.Numbers Alarm Spindle Station Cells Glyph Atlas
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius

variable {G : Gauge} {F : Family G} {N k i v p : ℕ} {b : ℝ} {x : Points v}

def q_asked {C:Family G}{d:Fin v→ℕ}(t:(i:Fin v)→ C.label (d i)): Fin v → C.book.Token:=fun i=>⟨d i,t i⟩

variable (C : Family G) (b : ℝ) (x : Points v) {d:Fin v → ℕ} (hN : k ≤ N) (p : ℕ)

def originX (k N p : ℕ) (v : (i:Fin v) → C.label (d i)):= Ship.clients C (q_asked (C:=C) v) b k N p x

def IssuedX (v : (i:Fin v) → C.label (d i)) := Array.stamp (Ship.yard C b hN p) (C.beta N p)
    (Read.bareP (originX C b x k N p v))
lemma stamp_singleX (s : (i:Fin v) → C.label (d i)) (i : Listens C b (v:=v) hN p) :
    (fun U=> (IssuedX C b x hN p s U).part (Glyph.slot i))= dot (fp C b hN p i)∘ Spindle.singleP C N p (s i.2) ∘ pull
      (hand C b hN p i) ((C.S.toDepth hN p).embed (seats C b x hN p i)) := by
  ext1 z
  let T:= Ship.yard C b hN p; let a:= fp C b hN p i; let V:= pull (T.omega i.1) (T.translateBy i.1) z
  rw [IssuedX,Array.stamp_part]
  have he : ∀ j : T.Cell,j≠i.1→ fibre j (Glyph.slot i)=Glyph.quiet _ := by
    intro j hj; apply Subtype.ext; ext m; simp [fibre, scene, Glyph.slot, Census.quiet, Census.fire];exact fun h=> hj (congr_arg Prod.fst h)
  rw [Finset.prod_eq_single i.1]; rotate_left
  · intro j _ hj
    rw [he j hj]; unfold Tiling.copy; split<;> simp [Read.bareP]
  · simp
  have hh : fibre i.1 (slot i)= slot i.2:= by apply Subtype.ext; ext m;rw [fibre_mem]; cases i; simp [slot,Census.fire]
  rw [hh]
  have hp (u:Config G (C.side N p)): (Read.bareP (originX C b x k N p s) u).part (slot i.2)=originX C b x k N p s i.2 u:= by simp [Read.bareP,Glyph.expand,slot,Census.fire]
  let v:= bare (C.beta N p) z
  change (v:ℂ) * T.copy _ _ _= _
  let δ:= T.omega i.1; let c :=T.translateBy i.1
  let f:= C.O N p (s i.2); let y:=location C.S k N p (Station.choose C.path.levels b k x i.2)
  have hq : (C.S.toDepth hN p).embed (seats C b x hN p i)= affine δ c y:= by
    unfold seats Peak.readers; rw [exact_camp]; simp only [ancestor, Ratio.embed_parent]; exact (exact_camp C b x p hN i).symm
  unfold Tiling.copy
  simp_rw [hp]; rw [Function.comp_apply,Function.comp_apply,hq]
  let pp:= affine δ c y
  let B:= bare (n:=C.side N p) (G:=G) (C.beta N p)
  have hx:C.O N p (s i.2) 0 (pull δ pp z)=f y (pull δ c z):= by
    rw [show pull δ pp z=pull 1 y (pull δ c z) by rw [pull_pull,mul_one],pull_one]
    rw [C.translation,zero_add]
  dsimp only [Spindle.singleP]; rw [bare_pull (C.beta N p) z]
  rw [show C.O N p (s i.2) 0 _=_ from (show C.O N p (s i.2) 0 (pull (hand C b hN p i) (affine δ c y) z)=_ from hx),dot_move]; congr 1


def BillsX (s : (i:Fin v) → C.label (d i)) (h : Course C N p k) := h.flow (IssuedX C b x hN p s) k hN

lemma origin_intX (s : (i:Fin v) → C.label (d i)) (i) : Continuous fun z => (Read.bareP (originX C b x k N p s) z).part i:= by
  simp_rw [Read.bareP,Glyph.expand]
  apply continuous_finsetProd _ fun j _=> C.continuousO _ _ _ _ _


end YM.Next.Rank.Edition