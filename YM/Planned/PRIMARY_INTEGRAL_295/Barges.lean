import YM.Planned.PRIMARY_INTEGRAL_295.Candles
import YM.Planned.PRIMARY_INTEGRAL_295.Dawning
/-!
# Exact oriented physical re-coloring of affine Window.Selection

Rotation vector on condensed Π intertwines b & support compression, even though C
may invert only locally. Handles all columns changing colors at a FIXED θ via ward
Matrix. In actual support Pose use Bank exact mid. no parameter deformation prices.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.PrimaryIntegral295.Barges
open Function Filter Set Metric MeasureTheory ProbabilityTheory Matrix Finset
open Lattice RG Wilson Pressure Labels Source Precision Exterior Tree Carrier Bloch Progress.StationaryScenes Bazaars Launch Shapes
open Villa Floor Glints Fizz Fizz.Gush Little Density Little.Core Push.Uniform Sparks  Hives Candles
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius RealInnerProductSpace
variable {G:Gauge}
variable {α X W : Type} [Fintype X] [DecidableEq X] [Fintype W] [DecidableEq W]

section Sharp
variable {H:Hive G X α} {J: Hive G W α} {e:W ↪ X}(h:Tracks J H e) (V:Windows e)
    {z:α→G.El}{A B:Matrix X X ℝ} (hA:Crown H H z z A B)
    (hy:∀ i, Full H (V.W i)) (ht:∀ i (j:G.ColorIndex), V.W i=V.W (J.pick i j))

def prism (A:Matrix X X ℝ):Matrix X W ℝ:= Matrix.of fun x i=> V.reed A i x

include h hA hy ht

omit h hA hy ht [Fintype X] [Fintype W] [DecidableEq W] in
private lemma reads (i j : W)(hi: V.W i= V.W j)(p:V.W i)(q:V.W i)(qf:q.val=e j)(A:Matrix X X ℝ):
     V.reed A j p.val= (V.chamber i A)⁻¹ p q:=by
   -- rewrite to generic formula with eq rec only on types & inverse.
   let f (a:X) (s:Finset X) (h:a∈s) (p:X):ℝ:=if hp:p∈s then (A.submatrix (Subtype.val:(s→_)) Subtype.val)⁻¹ ⟨_,hp⟩ ⟨_,h⟩ else 0
   suffices H:f (e j) (V.W j) (V.holds j) p.val = f (e j) (V.W i) (qf ▸ q.property) p.val by
     unfold f at H; rw [dif_pos p.property] at H; apply H.trans ?_; exact congrArg ((V.chamber i A)⁻¹ p) (Subtype.ext qf.symm)
   apply (show ∀ (s t:Finset X), s=t → ∀ (h:e j ∈s)(h': e j∈t), f (e j) s h p.val= f (e j) t h' p.val from by rintro s _ rfl _ _; rfl) _ _ hi.symm

lemma pronged : Crown H J z z (prism V A) (prism V B):=by
   ext x i; rw [H.pins,J.paws]
   by_cases hc : x ∈V.W i
   · let w:= V.W i
     let p:w:=⟨x,hc⟩; let q:w:=V.anchor i
     let h':= (interior H w (hy i)); let L := h'.paint z
     have hm:Crown h' h' z z (V.chamber i A)⁻¹ (V.chamber i B)⁻¹:= Crown.earns ((Tracks.tap (literal H w (hy i)) (literal H w (hy i)) hA))
     have hp : (L*(V.chamber i A)⁻¹) p q=((V.chamber i B)⁻¹*L) p q:= congr_fun (congr_fun hm p) q
     rw [show L=h'.paint z from rfl,h'.pins,h'.paws] at hp
     let i'(j):=J.pick i j
     let a(j):= h'.pick q j
     let b(j):= h'.pick p j
     have ha(j:G.ColorIndex): (a j).val=e (i' j) := h.picks i j
     have hS:= literal H w (hy i)
     have hL(j:G.ColorIndex): H.paint z x (H.pick x j) =L p (b j):= (Tracks.pace hS z p (b j)).symm
     have hY(j:G.ColorIndex): prism V A (H.pick x j) i= (V.chamber i A)⁻¹ (b j) q:=V.reed_inside A i (b j)
     have hR(j:G.ColorIndex): J.paint z (i' j) i=L (a j) q:=by
         rw [h.pace]
         change _=h'.paint z (a j) q
         have hℓ: h'.paint z (a j) q= H.paint z (a j).val (e i):= hS.pace z (a j) q; rw [hℓ,ha j]
     have hX(j:G.ColorIndex): prism V B x (i' j)= (V.chamber i B)⁻¹ p (a j) := reads V i (i' j) (ht i j) p (a j) (ha j) B
     simp_rw [hL,hY,show ∀ j,J.pick i j= i' j from fun j=>rfl,hX,hR]; exact hp
   have hf(j:G.ColorIndex) : prism V A (H.pick x j) i = 0:= V.reed_outside _ _ _ (fun H'=> hc (hy i _ H' _ (H.room_pick ..).symm))
   have hg(j:G.ColorIndex) : prism V B x (J.pick i j) = 0:= V.reed_outside _ _ _ (fun H'=> hc ((ht i j).symm ▸ H'))
   simp_rw [hf,hg, mul_zero,zero_mul]

lemma coincided : Crown J J z z (V.coin A) (V.coin B) :=by
   let v (A:Matrix X X ℝ): Matrix W W ℝ := (prism V A).submatrix e id
   have ht:Crown J J z z (v A) (v B):= h.tap (show Tracks J J id from ⟨fun _=>rfl⟩) (pronged h V hA hy ht)
   have hh(A:Matrix X X ℝ):V.coin A=(1/2:ℝ) • ((v A).transpose +v A):=by ext; rfl
   rw [hh,hh]; exact (ht.push.add ht).smul _
lemma morale (f:X→ℝ):
     J.burn z (V.morn A f)= V.morn B (H.burn z f):=by
   have ht:= (pronged h V hA hy ht).push.miles f
   have he (A:Matrix X X ℝ)(f:X→ℝ): V.morn A f= -((prism V A).transpose *ᵥ f):=by ext; rfl
   rw [he,he,map_neg,ht]
end Sharp

section Loom
open scoped Classical
variable {c f:Side} {S:StepData c f} (M:Bank G S)
def harp : Hive G M.keys (Bond f) := ⟨⟨M.move,fun _ _ h=>M.bee.injective (Subtype.ext h)⟩,fun x k=>(x.1,k),fun _ _=> rfl⟩

def harvest := family (Bond f) G
lemma heldFull : Full (harvest (f:=f) (G:=G)) M.grounds := by
   intro i hi j hj; change j.1=i.1 at hj; exact Finset.mem_product.mpr ⟨show j.1∈M.room from hj.symm ▸ (Finset.mem_product.mp hi).1,Finset.mem_univ _⟩

def housing : Hive G M.grounds (Bond f):= interior (harvest (f:=f) (G:=G)) M.grounds (heldFull M)
lemma inward : Tracks (harp M) (housing M) M.bee:=⟨fun _=>rfl⟩
lemma members (i:M.keys): Full (housing M) (M.homes.W i):= by
    intro j hj k hk; rw [M.inward] at hj ⊢; rw [show k.val.1=j.val.1 from hk]; exact hj
lemma stay (i:M.keys)(j:G.ColorIndex): M.homes.W i=M.homes.W ((harp M).pick i j) := by unfold Bank.homes; rfl

def head (A:Matrix (Acres f G) (Acres f G) ℝ):Matrix M.grounds M.grounds ℝ:=A.submatrix Subtype.val Subtype.val
lemma tilted {A B:Matrix (Acres f G) (Acres f G) ℝ} {z} (h:Crown harvest harvest z z A B) :
     Crown (housing M) (housing M) z z (head M A) (head M B):= Tracks.tap (literal _ M.grounds (heldFull M)) (literal _ M.grounds (heldFull M)) h
end Loom
end YM.Planned.PrimaryIntegral295.Barges
