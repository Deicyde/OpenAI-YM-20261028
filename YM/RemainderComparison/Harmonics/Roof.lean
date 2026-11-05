import YM.RemainderComparison.Harmonics.Budget
import YM.RemainderComparison.Creek.Ancient
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Harmonics
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter
open PhysicalNext.Repeat Deck Stellar Mint Poll Pond MeasureTheory ProbabilityTheory Greenbelt Lotus
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {c f C F L₀:Side} {P : Patch} {M : ℕ} {K : Teller G}
variable {h : f.val=c.val*P.L.val} {H : F.val=C.val*P.L.val} {Q:KernelChoices} {hC : C.val=c.val*M} {he:2 ≤ c.val}
local notation "L" => Lace.project (h:=h) (H:=H) hC he
local notation "S" => stepped Q h
local notation "Y" => stepped Q H
variable {T: Tube G (stepped Q h)} {T': Tube G (stepped Q H)} {p : ℝ} {E: Forest (stepped Q h).ratio} {E':Forest (stepped Q H).ratio}
    {X: Coat T E} {X': Coat T' E'} (A : Deck.Stellar hC he K p X X') {R:RG.Rep G f} {R':RG.Rep G F}
local notation "B" => radiusB p

variable (hC he) (I:Team R) (I':Team R')
variable {Z:Site C}{n:ℕ} {a W K₀ v : ℝ} {J : ConnectedActivityE6.Target G K} {o : ConnectedActivityE6.Target.Order G W}
    (C' : Cash W p a L₀ J o K₀ T' R') (c' : Cash W p a L₀ J o v T R) (hq : T'= re T)
    (ht : R'.path=R.path) (hx : R'.p=R.p) (hb:R'.beta=R.beta) (V:Molecule (stepped Q H))(U:Molecule (stepped Q h))
variable {hC he I I' V U}
variable (χ:Chi)
open Gas Ursell Trees Blaze March Lyric WickReps Creek Mosaic Merge Palette Typeface
variable {ι δ:Type}{α:Type*}(X:ι→Portrait R' α) (Y₁:δ→Portrait R α)(y:α)
local notation "X₁"=>brand X y
local notation "Z₁"=>brand Y₁ y
variable (s' : Sleet.Staff (brand X y) C') (s : Sleet.Staff (brand Y₁ y) c') (l:ι→ℝ)(l':δ→ℝ)(p₁:Set ι)(p₂:Set δ)(b₁ b₂:ℝ)
-- structural tie for any lexical correspondence. p notation locations pilot
variable (hC he)
structure Peers : Prop where
    chart : ∃ (t:ℕ)(z: Option (Fin t)→ C'.ThinP) (w : Option (Fin t)→ c'.ThinP) (i:Syllable X₁ C' ⟨t,z⟩) (j:Syllable Z₁ c' ⟨t,w⟩), s'=Sigma.mk ⟨t,z⟩ i ∧ s=Sigma.mk ⟨t,w⟩ j ∧
       ∀ v:Option (Fin t), ∀ r:α, Nonempty (Youth (p:=p) hC he (Merge.Palette.team (Typeface.brand Y₁ r) (j v)) (Merge.Palette.team (Typeface.brand X r) (i v)) (z v).val (w v).val) -- fix implicit S
variable {hC he}
variable (D' : Peers hC he C' c' X Y₁ y s' s)
-- χ not present, output χ.Free
local notation "T₀"=>Creek.theater C' χ X y l p₁ b₁
local notation "T₁"=>Creek.theater c' χ Y₁ y l' p₂ b₂
include D' ht C' c'
lemma logAreas : (T₁).halls s=((T₀).halls s').image ((L).low.cut):=by
    rcases D'.chart with ⟨k,z,w,i,j,he',hv,hb⟩; subst s'; subst s
    rw [Creek.point,Creek.point]; change univ.biUnion _= (univ.biUnion _).image _
    have hk u: c'.smallAt (w u) = (C'.smallAt (z u)).image ((L).low.cut) := Nonempty.elim (hb u y) fun p=> Youth.foldCount C' c' ht p
    ext l; constructor
    · intro h; obtain ⟨a,ha,hp⟩:=mem_biUnion.mp h; change l∈c'.smallAt (w a) at hp; rw [hk a] at hp; obtain ⟨i₀,hi,hx⟩:= mem_image.mp hp; exact mem_image.mpr ⟨i₀,mem_biUnion.mpr ⟨a,ha,hi⟩,hx⟩
    intro h; obtain ⟨a,ha,rfl⟩:=mem_image.mp h; obtain ⟨u,hu,hp⟩:=mem_biUnion.mp ha; exact mem_biUnion.mpr ⟨u,hu, show (L).low.cut a∈ c'.smallAt (w u) from (hk u).symm ▸ mem_image_of_mem _ (show a∈ C'.smallAt (z u) from hp)⟩
variable (hZ:2*(2*n+3)<c.val) (hS:(Creek.theater C' χ X y l p₁ b₁).halls s'⊆neighbors n Z)(V₀:Config G c)(hV : RG.flags (Pressure.temp p) V₀=∅)
variable {u u':ℕ}(A₀:Muse.Pad c' u χ)(A₁:Muse.Pad C' u' χ)
local notation "L₁"=>s'.fst
local notation "L₂"=>s.fst
include H ht D' A₀ A₁ hZ hS hx hb hq hV
lemma runProduct (r:α) : Lyric.string (Typeface.brand X r) C' χ L₁ s'.snd ((L).low.links V₀) = Lyric.string (Typeface.brand Y₁ r) c' χ L₂ s.snd V₀:=by
   obtain ⟨t,z,w,i,j,hz,hw,hp⟩:= D'.chart; subst s'; subst s
   rw [Creek.point] at hS; let y':= brand Y₁ r; let x':= brand X r
   have hp' v: C'.smallAt (z v)⊆neighbors n Z:= (Finset.subset_biUnion_of_mem (C'.smallAt ∘ z) (mem_univ v)).trans hS
   have hx' v:c'.smallAt (w v)=(C'.smallAt (z v)).image ((L).low.cut):= Nonempty.elim (hp v r) fun p=> Youth.foldCount C' c' ht p
   have ha : RG.flags (Pressure.temp p) ((L).low.links V₀)= ∅:=by ext i; rw [show i∈RG.flags (Pressure.temp p) ((L).low.links V₀) ↔ _ from flagged hC V₀ i (by have h:=c'.laws.data.room.buys; omega) (Pressure.temp p),hV]; simp
   have hᵥ a (V:Config G C) (hv:RG.flags (Pressure.temp p) V=∅): Healthy (Pressure.temp p) (C'.smallAt (z a)) V:=by unfold Healthy; simp [hv]
   change Lyric.string x' C' χ ⟨t,z⟩ i _=Lyric.string y' c' χ ⟨t,w⟩ j _; unfold string; apply congr_arg₂ (·*·)
   · apply congr_arg (fun a:ℝ=>a / (↑(t+1).factorial :ℝ)) (Meadow.movement C'.seam z c'.seam w _); intro a b
     have he {c f L₀:Side}{S' : StepData c f}{T : Tube G S'}{R : RG.Rep G f} {a v :ℝ}(H : Cash W p a L₀ J o v T R)(u v:H.ThinP): H.seam u v ↔ Ac.meets H.smallAt v (H.smallAt u):= by
        refine ⟨fun he=>?_, Or.inr⟩; rcases he with h|h; swap; exact h
        obtain ⟨k,hk⟩:=u.prop.1; subst u; exact ⟨k,hk,hk⟩
     rw [he,he]; change (∃ p∈C'.smallAt (z a), p∈C'.smallAt (z b))↔ ∃ p∈ c'.smallAt (w a),p∈ c'.smallAt (w b); rw [hx',hx']
     constructor
     · rintro ⟨x,h,h'⟩; exact ⟨_,mem_image_of_mem _ h,mem_image_of_mem _ h'⟩
     rintro ⟨x,h,h'⟩; obtain ⟨i',hi,hp''⟩:= mem_image.mp h'; obtain ⟨j',hj,hh⟩:=mem_image.mp h
     have hs i (hi:i∈neighbors n Z): reverts hC Z ((L).low.cut i)=i:= same_site hC Z _ (by omega) (Finset.Subset.refl _) i hi -- inferred
     exact ⟨i', ((hs j' (hp' _ hj)).symm.trans ((congr_arg _ (hh.trans hp''.symm)).trans (hs i' (hp' _ hi)))) ▸ hj,hi⟩
   refine Finset.prod_congr rfl fun v _=>?_
   have htV:= Lyric.flagged_step x' C' χ A₁.S.N (z v) (i v) ((L).low.links V₀)
   have htY:= Lyric.flagged_step y' c' χ A₀.S.N (w v) (j v) V₀
   rw [masked_eq _ _ _ _ (hᵥ v _ ha)] at htV; rw [masked_eq _ _ _ _ (show Healthy (Pressure.temp p) (c'.smallAt (w v)) V₀ from (by unfold Healthy; simp [hV]))] at htY
   exact htV.symm.trans ((Nonempty.elim (hp v r) fun p=> Youth.farm C' c' hq ht hx hb p hZ (hp' v) V₀ χ hV).trans htY)
open WickReps
variable (r:α)
local notation "Lt"=>Muse.sits p₁ l b₁
local notation "Lt'"=>Muse.sits p₂ l' b₂
-- syntax position power norm ΩE exposed
lemma traversed (d:ℝ)(hp : Lyric.invests (Typeface.brand X y) C' s'.1 s'.2 (Muse.sits p₁ l b₁)= d * Lyric.invests (Typeface.brand Y₁ y) c' s.1 s.2 (Muse.sits p₂ l' b₂)) : (T₀).solvent r s' ((L).low.links V₀)= d* (T₁).solvent r s V₀:=by
  let g:= Lyric.string (Typeface.brand Y₁ r) c' χ s.1 s.2 V₀
  change ((etude (Typeface.brand X r) C' χ s'.1 s'.2).stock Lt)*_=_*((etude (Typeface.brand Y₁ r) c' χ s.1 s.2).stock Lt' * g)
  rw [Mosaic.pieces (Typeface.brand Y₁ r) c' χ Lt' s.fst s.snd] -- instead
  have hx:=(runProduct C' c' hq ht hx hb χ X Y₁ y s' s l p₁ b₁ D' hZ hS V₀ hV A₀ A₁ r)
  rw [Mosaic.pieces _ _ _ Lt _ _]; change invests X₁ C' s'.1 s'.2 Lt * Lyric.string _ _ _ _ _ _ = d*(invests Z₁ c' s.1 s.2 Lt'*g); rw [hx,hp,mul_assoc]
end YM.RemainderComparison.Harmonics
