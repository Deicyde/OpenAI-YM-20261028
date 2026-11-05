import YM.RG08.Flat.Shadow

/-!
# Flat precision receipt at compatible pre-length, then on demanded steps
-/
noncomputable section
namespace YM.RG08.Flat
open Filter Finset Pert.Bulk Laurent Lattice Bloch Stationary Function Matrix RG08.Packets RG08.Rate RG Precision Next.Free Exterior
open scoped Topology ENNReal
set_option autoImplicit false
variable {G : Gauge} {a:Levels G}

structure Quorum (w : ℕ → ℝ) (F : ℕ→Kernel Links Links) (e:ℕ) (H : Horizon a) (A B:ℝ)(d l:ℕ)(c:ℝ) : Prop where
  logged : 0≤A
  bulk : 0≤B
  positive : 0<c
  frames k i : e ≤ i →
    RowCost (w (a.clock.J i)) 1 (F i) (B*clock a.S (Lambda' a) k i ^l)
  converges i : e ≤ i → ∀ m z,Tendsto (fun n=> output (H.H n i) m z) atTop (𝓝 (F i m z))
  approximates k i N : e ≤ i → i ≤ N →
    RowCost (w (a.clock.J i)) 1 (fun x z=>output (H.H N i) x z-F i x z) (A*clock a.S (Lambda' a) k i^d * ((a.S.a N/a.S.a i)^c))

/-- The length threshold here independent of all block ratios, including on precedents. Keep it
as a **global** requirement from scale zero (to cover even auxiliary Dirac/clip data used in proof
of this formal estimate; threshold can depend on the demand through P upstream); the polynomial
cap need only apply on the admitting tail. For the flat 0 supply here, these additional gates are
independent of later and higher-order demands. -/
theorem entrance_gate (hg:G.Simple)(K:KernelChoices)(s:Supply.Sheet G)(hS:s.kernel=K) :
    ∃ (X : MapPrices)(E:ℕ→ℕ), ∀ a:Levels G,a.clock.kernel=s.kernel → -- may keep s.profile distinct, need new Sheet for adjust
      a.clock.stage=s.profile →
      (∀ i,E (a.clock.J (i+1)) ≤ (a.S.block i).val) → ∀ e, Delay a X e →
        ∃ (F:ℕ→Kernel Links Links)(A B:ℝ)(d l:ℕ)(c:ℝ), ∀ (H:Horizon a)(P:MapPrices), H.Suffices P → Quorum (curve X) F e H A B d l c := by
  classical
  obtain ⟨q,o,γ,n,HC,HK⟩:= retained_support (G:=G) K
  let s' := {s with profile:=fun i=> rearrange (s.profile i) (γ i) (HC.fit i)}
  obtain ⟨X,ht⟩ := HK s' hS
  let E j := max (tickets X j) (n j)
  refine ⟨X,E,fun a ha hs hE e hp=> ?_⟩
  let b:= shadow a γ HC.fit
  have hC : Credit b γ n := ⟨fun _=>le_rfl,fun i=> (Nat.le_max_right ..).trans (hE i)⟩
  have hz : b.clock.stage=s'.profile := by funext i; unfold b shadow adjust s'; simp only [hs]
  obtain ⟨_,Y,-,-,-,hY,H',-⟩:= ht b ha hz hC
  have hs' := spacing_choice (a:=b) hg X (fun i _=> (Nat.le_max_left ..).trans (hE i)) (show Delay b X e from hp)
  obtain ⟨F,A,B,d,l,c,hA,hB,hc,H⟩:=supplies hs' hY (fun i N _ he=> (H'.2 N i he).2)
  refine ⟨F,A,B,d,l,c,fun T P hT=> ⟨hA,hB,hc,fun k i hi=> (H k i hi).1, fun i hi m z => ?_,fun k i N hi hh=>?_⟩⟩
  · exact ((H 0 i hi).2.1 m z).congr' ((eventually_ge_atTop i).mono fun t ht=>by
      change output (Y.H t i) _ _=output (T.H t i) _ _
      rw [same_shadow a γ HC.fit hT hY t i ht])
  simp_rw [same_shadow a γ HC.fit hT hY N i hh]
  exact (H k i hi).2.2 _ hh
end YM.RG08.Flat
