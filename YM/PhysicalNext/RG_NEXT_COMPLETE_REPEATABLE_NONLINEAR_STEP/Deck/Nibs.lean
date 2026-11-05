import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Deck.Sylvan
/-! # Condensation log and Gram marginal covariance. Coinvariant E6 tiles.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Deck.Stellar
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval
variable {G : Gauge} {c f C F:Side} {P : Patch} {M D' : ℕ} {K : Teller G}
variable {h : f.val=c.val*P.L.val} {H : F.val=C.val*P.L.val} {Q:KernelChoices} {hC : C.val=c.val*M} {he:2 ≤ c.val}
local notation "L" => Lace.project (h:=h) (H:=H) hC he
local notation "S" => stepped Q h
local notation "Y" => stepped Q H
variable {T: Tube G (stepped Q h)} {T': Tube G (stepped Q H)} {p : ℝ} {E: Forest (stepped Q h).ratio} {E':Forest (stepped Q H).ratio}
    {X: Coat T E} {X': Coat T' E'} (A : Stellar hC he K p X X')
local notation "B" => radiusB p
include A
lemma white : Stellar hC he K p X.blank X'.blank:= ⟨rfl,rfl,A.equal,A.reached,A.clips,A.wit,rfl,A.tree,A.reach,A.old,A.wall,A.tall,A.news⟩
lemma flagellum (p' : Bond F): Batch.joint X'.plate X'.shutter p'= Batch.joint X.plate X.shutter (curr (L).high.cut p'):= by
  unfold Batch.joint; refine sum_congr rfl fun i hi=>?_ ; unfold Pulse.localBase;
  let j := (p',i); let W:=X'.shutter.take j; let z:=seed (L) (G:=G) j; let u:=X.shutter.take z
  apply congr_arg (fun f:ℝ→ℝ=> ∫ x in (0:ℝ)..1,f x); ext s
  change intensity _ _ s _ j j=intensity _ _ s 0 z z; let y:=X'.plate; let w:= X.plate
  rw [Batch.perWindow y X'.shutter j s (W:=W) rfl (X'.shutter.here _),Batch.perWindow w X.shutter z s (W:=u) rfl (X.shutter.here _)]
  let J:↥W:=⟨j,X'.shutter.here _⟩; let Z:↥u:= ⟨z,X.shutter.here _⟩
  obtain ⟨f,hx⟩:= A.derby j
  let X g:= Batch.principal u g; let X' g:= Batch.principal W g; let e (g:Matrix (↥u) (↥u) ℝ):=g.submatrix f f
  have he : X' y=e (X w):=A.prospers _ f hx; have h₁ : X' (y-1)= e (X (w-1)):= by
    unfold e X' X Batch.principal -- reorder
    simp only [submatrix_sub]; change X' y-Batch.principal W (1:Matrix ..) = e (X w)-e (Batch.principal u (1:Matrix ..)); rw [he,Batch.within_one,Batch.within_one]; unfold e; rw [Matrix.submatrix_one_equiv]
  have hc : X' (glide y s)=e (X (glide w s)):= by
    unfold X' X Batch.principal glide e
    simp only [submatrix_add, submatrix_smul]; change Batch.principal W (1:Matrix ..) + s • X' (y-1)=e (Batch.principal u (1:Matrix ..))+ s • e (X (w-1)); rw [h₁, Batch.within_one,Batch.within_one]; unfold e; rw [Matrix.submatrix_one_equiv]
  have hZ : f J=Z:=Subtype.ext (hx J)
  change (X' (y-1)*(X' (glide y s))⁻¹) J J=(X (w-1)*(X (glide w s))⁻¹) Z Z
  rw [hc,h₁]; unfold e; rw [Matrix.inv_submatrix_equiv,submatrix_mul_equiv,Matrix.submatrix_apply,hZ]
lemma crowns (t:Bond F): X'.condensation t = X.condensation (curr (L).high.cut t):= congr_arg₂ (·/·) (congr_arg₂ (·-·) (A.white.flagellum t) (A.flagellum t)) rfl
end YM.PhysicalNext.Repeat.Deck.Stellar
