import YM.MergeProof.West.Brite
import YM.MergeProof.West.Coke
import YM.MergeProof.West.Equity
import YM.MergeProof.West.Jolly
import YM.PhysicalNext.RG_NEXT_ALL_FIELD_EXPANSION_DERIVATIVES.TagsHood



/-!
# Uniform Bleaching/sensed and numeric gates over compacta of the configuration space
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Tapes.West
open Function Lattice Wilson RG Perch Atlas Rise Normal Ribbon Spindle Glyph Exponential MvPolynomial Camp Peak Station Ac Alarm Thirst Corona Value Relation Finset Marker
open MeasureTheory Cells Edition Filter Paint Vac.Numbers Prayer Glimmer Read
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius
variable {G:Gauge} {C:Family G}{N n p k m u D:ℕ}{ξ:Purse}{R:Lead G C.S p} {c:Course C N p k}{P:(i:ℕ)→ Rep G (C.side i p)}{s z:ℝ}{Ψ:AtlasData G C.S p}
section
variable (A:Levels G){x : Points n} {K:Set (Points n)}
set_option linter.unusedVariables false
lemma maxim {B:ℕ→ Points n → Prop} {Y:ℕ → Points n→Points n} (hK:IsCompact K)
    (hp:∀ (x:Points n),x∈K →∀ (ζ:ℕ→ℕ),Tendsto ζ atTop atTop→∀ (v:ℕ → Points n),Tendsto (fun i=>Y (ζ i) (v i)) atTop (𝓝 x) → ∀ᶠ k in atTop, B (ζ k) (v k)) : ∀ᶠ k : ℕ in atTop, ∀ x:Points n,Y k x∈K→B k x:=by
   by_contra hf
   have hh(z:ℕ):∃ k, z≤k∧ ∃ x,Y k x∈K∧¬B k x:=by
      by_contra! he
      apply hf; refine eventually_atTop.2 ⟨z,fun k hk x hv=> by simpa using he k hk x hv⟩
   choose ζ hz v hv hg using hh
   obtain ⟨x,hx,p,hP,hV⟩:= hK.isSeqCompact (x:=fun i=> Y (ζ i) (v i)) hv
   have hT:Tendsto ζ atTop atTop:= tendsto_atTop_mono hz tendsto_id
   obtain ⟨j,hj⟩:= (hp x hx (ζ ∘ p) (hT.comp hP.tendsto_atTop) (v ∘ p) hV).exists
   exact hg (p j) hj
end
variable {K:Set (Points n)} {d:ℕ}{d0:Fin n→ℕ}(h:∀ i,d0 i≤ d)(w:(i:Fin n)→ C.label (d0 i))
set_option quotPrecheck false
local notation "AΩ" => C.path.levels
structure Walls (b:ℝ)(h:∀ i,d0 i ≤ d)(w:(i:Fin n)→ C.label (d0 i))(K:Set (Points n))(D k:ℕ):Prop where
   merry (x:Points n)(hx:tested C.path.levels b k x ∈ K): Balcon b h w x k D
   replies x : tested C.path.levels b k x∈K →∀ hk:Fit C.path.levels b k x, Allowed C.path.levels b k →
       (∀ p N (hN:k≤N),Spaced (scouts C k) (seats C b x hN p)) ∧
       ∀ p Ψ,Wall.Vantage C.path.levels d k p n D b Ψ → Bell C.path.levels Ψ d D hk
lemma mural_cast (hK:IsCompact K)(hx:K ⊆ conf _)(H:C.Makes)(he:G.Simple) (b:ℝ)(hb:6 ≤ b)(hs:∀ i,saves C (d0 i)+3 ≤ b) (D:ℕ) : ∀ᶠ k in atTop,Walls b h w K D k:=by
   let Y (k:ℕ) x:= tested AΩ b k (x:Points n); have hr:0 < b:=by linarith
   have hp:∀ᶠ k in atTop, ∀ x:Points n, Y k x∈K→ Balcon b h w x k D:=by
      apply maxim hK; intro x hg ζ hz v hV; let W:=jointX w
      have he' := hx hg
      filter_upwards [hz.eventually (passingX_all he H D h w b hr hs),clockwiseX D AΩ he hr x he' ζ hz v hV d,coughX (C:=C) he hr x he' W ζ v hz hV,
         Glimmer.accumulate ℕ atTop (fun i=> Read.maxProfile C (Y (ζ i) (v i)) W) (Read.maxProfile C x W) (profile_tends _ _ (Maxwell.table_smooth C.labels) he' hV) _ ((hat_rate AΩ he).comp hz)] with k H1 H2 H3 H4
      exact ⟨H1,H3,H2,H4⟩
   let V k (x:Points n) (h:Fit C.path.levels b k x) : Prop := Allowed C.path.levels b k →
       (∀ p N (hN:k≤N),Spaced (scouts C k) (seats C b x hN p)) ∧
       ∀ p Ψ,Wall.Vantage C.path.levels d k p n D b Ψ → Bell C.path.levels Ψ d D h
   have hz:∀ᶠ k in atTop,∀ x:Points n, Y k x∈K→ ∀ h, V k x h:=by
      apply maxim hK; intro x hg ζ hz v hV; filter_upwards [Wall.on_hold AΩ b D d he (hx hg) hb ζ hz v hV,Edition.riseX C x he (hx hg) hr ζ v hz hV] with k hC HH h1 h2
      exact ⟨HH h1 h2,hC h1 h2⟩
   filter_upwards [hp,hz] with k hP hV
   exact ⟨hP,hV⟩
end YM.Next.Rank.Tapes.West
