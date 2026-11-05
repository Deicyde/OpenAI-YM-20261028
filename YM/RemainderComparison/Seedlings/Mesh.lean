import YM.RemainderComparison.Seedlings.Sailor
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Seedlings
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter
open PhysicalNext.Repeat Deck Stellar Mint Poll Pond MeasureTheory ProbabilityTheory Greenbelt Lotus
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {c f C F L₀:Side} {P : Patch} {M : ℕ} {K : Teller G}
variable {h : f.val=c.val*P.L.val} {H : F.val=C.val*P.L.val} {Q:KernelChoices} {hC : C.val=c.val*M} {he:2 ≤ c.val}
variable {T: Tube G (stepped Q h)} {T': Tube G (stepped Q H)} {p : ℝ} {E: Forest (stepped Q h).ratio} {E':Forest (stepped Q H).ratio}
    {R:RG.Rep G f} {R':RG.Rep G F}

variable (hC he) (I:Team R) (I':Team R')
variable {Z:Site C}{n:ℕ} {a W K₀ v : ℝ} {J : ConnectedActivityE6.Target G K} {o : ConnectedActivityE6.Target.Order G W}
    (C' : Cash W p a L₀ J o K₀ T' R') (c' : Cash W p a L₀ J o v T R) (hq : T'= re T)
    (ht : R'.path=R.path) (hx : R'.p=R.p) (hb:R'.beta=R.beta) (V:Molecule (stepped Q H))(U:Molecule (stepped Q h))
variable {hC he I I' V U}
variable (χ:Chi)
open Gas Ursell Trees Blaze March Lyric WickReps Creek Mosaic Merge Palette Typeface
open Harmonics
namespace BoxOf
variable {ι δ:Type}{α:Type*}(X:ι→Portrait R' α) (Y₁:δ→Portrait R α)(y:α)
variable (K':BoxOf C') (D':BoxOf c') (b:Finset ι)(b':Finset δ)
variable (x:Site c) (r n':ℕ)
variable (l:ι→ℝ)(l':δ→ℝ)(Gm:Set ι)(Δ:Set δ)(b₁ b₂:ℝ)
variable (x':Site C)
-- Both real and θ use Λ.Vvol. Require agreement only through larger genuine R. No scale or price estimates on intermediary unless those purchased across all suitably employed further volumes.
-- does not require sums P.C outcome equality as hypothesis.
structure Mesh (d:ℝ) : Prop where
   panels : ∃ (v:Side)(N:Side) (m m':ℕ)(hi:N.val=v.val*P.L.val)(hv:v.val=c.val*m)(ht:v.val=C.val*m') (_:2*(2*r+3)<C.val) (_:2*(2*r+3)<c.val)
          (v₁:2≤c.val) (v₂:2≤ C.val) (R'':RG.Rep G N) (T'':Tube G (stepped Q hi))(U:ℝ)(I:Cash W p a L₀ J o U T'' R'')
          (F':BoxOf I) (S:Type) (M:S→ Portrait R'' α) (Z: Finset S)(lM:S→ℝ)(YM:Set S)(x₀:ℝ),
           Port ht v₂ I C' M X y F' K' Z b x' r n' lM l YM Gm x₀ b₁ 1 ∧
           Port hv v₁ I c' M Y₁ y F' D' Z b' x r n' lM l' YM Δ x₀ b₂ d ∧ SliceRows.Stamp T''
-- missing hypothesis universal Warm.Record.Pose acquired. Provide lemma ALL when price Clock
variable (Sg: ℝ→ Prop)
-- grouping with hr.D roses.E.Material.Post.Cookie
structure Enlightened (Q:KernelChoices)(P:RG.Patch)(T:Teller G) (J:ConnectedActivityE6.Target G T)(o:Target.Order G W)(x a:ℝ) (L:Side)(χ:Chi):Prop where
    warm (c f: Side)(hc:f.val=c.val*P.L.val) (T': Tube G (stepped Q hc)) (R:RG.Rep G f)(p:ℝ) (C:Cash W x a L J o p T' R) : SliceRows.Stamp T' → Bloom C χ
-- Actually Aura Weather funding requires Stamp T; can condition on inherited Stamp P Basic.T. which Peers across BOTH gives. adjust.
variable (H':Enlightened Q P K J o p a L₀ χ) (d:ℝ)(hh:Mesh C' c' X Y₁ y K' D' b b' x r n' l l' Gm Δ b₁ b₂ x' d)
variable (hk:SliceRows.Stamp T)(hv₀:SliceRows.Stamp T')
include hk hv₀ H' hh
lemma watershed (A:Config G c)(B:Config G C)(hA: flags (Pressure.temp p) A=∅)(hB: flags (Pressure.temp p) B=∅)(hv:Agrees (Lattice.box r) (expandAt x A) (expandAt x' B))(u:α):
    pool X y C' b K' x' r n' χ l Gm b₁ u B=d*pool Y₁ y c' b' D' x r n' χ l' Δ b₂ u A∧ flagsCollected X y C' b K' r n' χ l Gm b₁ u x' B=d*flagsCollected Y₁ y c' b' D' r n' χ l' Δ b₂ u x A:=by
   rcases hh.panels with ⟨C₀,F₀,k,k',hol,hy,hC,hE,hU,hq,ht,R₁,T₁,L,L',I,Hs,Vx,w,e,E,bK,hR,hF,hS⟩
   let U:= Lace.project (h:=h) (H:=hol) hy hq; let U':= Lace.project (h:=H) (H:=hol) hC ht
   obtain ⟨h₁,h₂⟩:= barge hy hq L' c' χ Vx Y₁ y I D' w b' x r n' e l' E Δ bK b₂ _ hF (H'.warm _ _ _ _ _ _ _ hS) (H'.warm _ _ _ _ _ _ _ hk) hU A hA u
   obtain ⟨h₃,h₄⟩:= barge hC ht L' C' χ Vx X y I K' w b x' r n' e l E Gm bK b₁ _ hR (H'.warm _ _ _ _ _ _ _ hS) (H'.warm _ _ _ _ _ _ _ hv₀) hE B hB u -- b name shadow
   let V:= U.low.links (Lattice.translate x A); let W:= U'.low.links (Lattice.translate x' B)
   have he: Agrees (neighbors r (0:Site C₀):Set (Site C₀)) W V:=by
       apply Slide.readNear (x:=(0:Site C₀)) (by
         have hp: 0<k':=by
            by_contra he; have hh:k'=0:=Nat.eq_zero_of_not_pos he
            rw [hh,mul_zero] at hC; have hp:= C₀.pos; omega
         have he:C.val≤ C₀.val:= hC ▸ Nat.le_mul_of_pos_right _ hp; omega)
       have hg : expandAt 0 W=expandAt x' B:=by
          rw [show expandAt 0 W=_ from Slide.rolls hC (Lattice.translate x' B) (0:Site C₀), map_zero,Slide.increases]
       rw [hg, show expandAt 0 V= _ from Slide.rolls hy (Lattice.translate x A) (0:Site C₀),map_zero,Slide.increases]; exact fun i h h' => (hv i h h').symm
   have hV : LocalOn (neighbors r (0 : Site C₀): Set (Site C₀)) (BoxOf.flagsCollected Vx y L' w I r n' χ e E bK u 0):=by rw [BoxOf.bound]; exact BoxOf.applause _ _ _ _ _ _ _ _ _ _ _ _ u (H'.warm _ _ _ _ _ _ _ hS)
   rw [one_mul] at h₃ h₄; rw [← h₃, ← h₄]; exact ⟨((BoxOf.polar Vx y L' w I 0 r n' χ e E bK u (H'.warm _ _ _ _ _ _ _ hS) W V he).trans h₁), ((hV W V he).trans h₂)⟩
end BoxOf
end YM.RemainderComparison.Seedlings
