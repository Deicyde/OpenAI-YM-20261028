import YM.MergeProof.West.View
import YM.TraceExtension.Prom.Hill.Allowance
import YM.TraceExtension.Prom.Hill.Camps
import YM.TraceExtension.Prom.Hill.Joints
import YM.TraceExtension.Prom.Hill.Memorandum
import YM.TraceExtension.Prom.Hill.Station
/-!
  Variant of YM.MergeProof.West.View for dynamic stops. Pulse extension.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Tapes.West
open Function Lattice Wilson RG Perch Atlas Rise Normal Ribbon Spindle Glyph Exponential MvPolynomial Camp Peak Cells Station Ac Alarm Thirst Corona Value Finset MeasureTheory Edition
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius

variable {G : Gauge} {B : Side}
variable {S : Schedule} {C : Family G} {A : Levels G} {i k l j m p q D N d n : ℕ}
variable (x : Points n) (s : ℝ)

abbrev BaleSky (C : Family G) (k : ℕ) (s : ℝ) (p : ℕ) (d : ℕ) (x : Points n) {i} (hk : i≤k):= CellPSky C k s p × PatchPt x s C.path.levels p d hk

def d_olmSky (q B : ℕ) (hN : k≤N) (hk : i≤k) (u : CellPSky C k s p) (t : Manner n) :=
    Spindle.patch (q*B) (readersSky (C:=C) (b:=s) (p:=p) x hN (hk.trans hN) (u,Head t))

def litFtSky {G : Gauge} (p : ℕ) (_ : k≤N) (b : ℝ) (C : Family G) (u : CellPSky C k b p) (x : Manner n) := sectionAt (u,tag x)
lemma torchesSky (hN : k ≤ N) (s : ℝ) (p : ℕ) : Injective fun i : CellPSky C k s p × Manner n => litFtSky p hN s C i.1 i.2 := by
  rintro ⟨a,u⟩ ⟨b,v⟩ h
  change Glyph.push _ _ = Glyph.push _ _ at h
  obtain ⟨z,hz⟩:= (tag u).property
  have ht : (a,z)∈ (Glyph.push b (tag v).val).val:= h ▸ Finset.mem_product.mpr ⟨mem_singleton_self a,hz⟩; replace ht:=mem_singleton.mp (mem_product.mp ht).1
  subst b
  have he : tag u=tag v:= Subtype.ext (Subtype.ext (Finset.Subset.antisymm ?_ ?_)); rotate_left
  · intro i hi; exact (mem_product.mp (show (a,i)∈({a} ×ˢ (tag v).val.val : Finset _) from (show (a,i)∈(Glyph.push a _).val from h ▸ (show (a,i)∈(Glyph.push a (tag u).val).val from mem_product.mpr ⟨mem_singleton_self _,hi⟩)))).2
  · intro i hi; exact (mem_product.mp (show (a,i)∈({a} ×ˢ (tag u).val.val : Finset _) from (show (a,i)∈(Glyph.push a _).val from h.symm ▸ (show (a,i)∈(Glyph.push a (tag v).val).val from mem_product.mpr ⟨mem_singleton_self _,hi⟩)))).2
  exact congr_arg _ (show _=_ from he)

-- orphan singleton always present. hMask center inherited exactly before κ formation.

private lemma registersSky (hN : k≤N) (hi : i ≤ k) (j : BaleSky C k s p d x hi) :
    (litFtSky p hN s C j.1 j.2.val).val.Nonempty:= by
  obtain ⟨i,hi⟩:= (tag j.2.val).property; exact ⟨(j.1,i),mem_product.mpr ⟨mem_singleton_self _,hi⟩⟩
lemma prizeFtSky (hN : k≤N) (h : i ≤ k) (H : middleSky C.path.levels s k≤ i) (O : roomTestSky C.path.levels s k p d q)
    (j : BaleSky C k s p d x h) (a : CellPSky C k s p×Fin n) (ha : a∈ (litFtSky p hN s C j.1 j.2.val).val):
     readersSky (C:=C) (b:=s) (p:=p) x hN (h.trans hN) a ∈ d_olmSky x s q (walls (clim C.path.levels i)) hN h j.1 j.2.val:= by
  apply doors _|>.2; rcases j with ⟨j,t,hT⟩; obtain ⟨z,b⟩:= a
  have he:=mem_product.mp ha; replace ha:=he.2; have hp:b∈(tag t).val.val:=ha; have hC:z=j:= mem_singleton.mp he.1; subst z
  refine le_trans (le_of_eq (togetherSky x s p hN h ((Station.widerSky ..).trans H) j (Head t) b)) ?_
  exact (hT (Head t) (head_member t) b hp).trans (Nat.mul_le_mul_right (walls (clim C.path.levels i)) ((Nat.le_add_right d 10).trans O.radius))

lemma n_earbySky (h : i≤k) (u : Manner n) (c : Chamber G C.S i p) (hh : spotFt s i d h (C:=C) x u c) (V : roomTestSky C.path.levels s k p d q) :
    separation (core C.path.levels x s p h (Head u)) c.1+2 ≤ q*walls (clim C.path.levels i):= by
  let r:= walls (clim C.path.levels i); let l:=core C.path.levels x s p h (Head u)
  change separation l c.1+2≤ q*r; change separation l c.1≤(d+8)*r at hh; have ht : 1≤ r:= fifth C.path.levels _
  linarith only [ht, Nat.mul_le_mul_right r V.radius,hh]

def gloryFtSky (p : ℕ) (hN : k≤N) (hk : i≤k) (hi : middleSky C.path.levels s k ≤ i) (H : CellPSky C k s p) (j : Manner n) (c : ℝ) (P : poly (Chamber G C.S i p)) :=
  let T:= Ship.yardSky C s hN p; let R:=core C.path.levels x s p hk (Head j); let A:= watchesSky C s p hN i hi H
  Edition.dot (T.hand H) ∘ caseW P R c ∘ A
lemma seenPSky (p) (hN : k≤N) (hk : i≤k) (hi : middleSky C.path.levels s k ≤ i) (a : CellPSky C k s p) (j : Manner n) (q B : ℕ) :
    d_olmSky x s q B hN hk a j=swath ((Ship.yardSky C s hN p).omega a) (spreadCSky C s p ((Station.widerSky ..).trans hi) a) (Spindle.patch (q*B) (core C.path.levels x s p hk (Head j))):= by
  unfold d_olmSky Spindle.patch; rw [fillsSky C x s p hN hk ((Station.widerSky ..).trans hi),swath_iffHalo]; simp only [swath, image_singleton];rfl

def mimicFtSky (p : ℕ) (hN : k≤N) (hk : i≤k) (hi : middleSky C.path.levels s k ≤ i) (V : roomTestSky C.path.levels s k p d q) (j : BaleSky C k s p d x hk) (P : poly (Chamber G C.S i p)) (c : ℝ) (h : ∀ i'∈ P.vars,spotFt (C:=C) s i d hk x j.2.val i') (hp : Poetic P) :
    SourceAt G (readersSky (C:=C) (b:=s) (p:=p) x hN (hk.trans hN)):= by
  let T:= Ship.yardSky C s hN p; let A:=C.path.levels; let B:=walls (clim A i); let q':=q*B; let a:= core A x s p hk (Head j.2.val)
  let Q:= watchesSky C s p hN i hi j.1
  have ht := case_in P hp c (fun i hI=>n_earbySky x s hk _ i (h _ hI) V) (V.suite i hi hk)
  refine ⟨d_olmSky x s q B hN hk j.1 j.2.val,litFtSky p hN s C j.1 j.2.val,registersSky x s hN hk j,fun a=>prizeFtSky x s hN hk hi V j a, gloryFtSky x s p hN hk hi j.1 j.2.val c P,?_,?_,?_⟩
  · have he:Continuous Q:=continuous_pull ..; exact (dot_meas _).comp ((case_meas _ _ _).measurable.comp he.measurable)
  · rw [seenPSky x s p hN hk hi]; exact fun U V h=> congr_arg (dot _) (p_local _ _ _ ht.1 U V h)
  exact fun v U=>congr_arg (dot _) (p_invar _ _ ht.2 v U)

end YM.Next.Rank.Tapes.West
