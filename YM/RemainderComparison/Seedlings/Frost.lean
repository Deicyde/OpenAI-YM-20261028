import YM.RemainderComparison.Seedlings.Motion
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
local notation "L" => Lace.project (h:=h) (H:=H) hC he
local notation "S" => stepped Q h
local notation "Y" => stepped Q H
variable {T: Tube G (stepped Q h)} {T': Tube G (stepped Q H)} {p : ℝ} {E: Forest (stepped Q h).ratio} {E':Forest (stepped Q H).ratio}
    {R:RG.Rep G f} {R':RG.Rep G F}
local notation "B" => radiusB p

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
local notation "X₁"=>brand X y
variable (hC he)
local notation "Z₁" => brand Y₁ y
variable (K':BoxOf C') (D':BoxOf c') (b:Finset ι)(b':Finset δ)
variable (x:Site C) (r n:ℕ)(W' : Warp («S»:= stepped Q H) b b' (S':=stepped Q h))
set_option quotPrecheck false
local notation "uₓ"=> (L).low.cut x

-- lexical elements only, geometry fields to see any mask & enforcers. port.X.No cost expected.
structure Folding : Prop where
   signed : Set.InjOn W'.f (↑(hub X y C' b K' x r n) : Set (Head (stepped Q H)))
   halos : (nearby C' K' x r n).image W'.f=nearby c' D' ((Lace.project (h:=h) (H:=H) hC he).low.cut x) r n
   largeSkin : W'.halo=(Lace.project (h:=h) (H:=H) hC he).low.cut
   memories (i : ↥b) : Palette.sign (Typeface.brand Y₁ y) (stepped Q h) (W'.grow i).val=W'.f (Palette.sign (Typeface.brand X y) (stepped Q H) i.val)∧ ∃ p,(Typeface.brand X y i.val).turn=Wing.logKey p ∧ ∃ p',(Typeface.brand Y₁ y (W'.grow i).val).turn=Wing.logKey p'
   items (i:↥b) : ∀ u:α, (Typeface.brand Y₁ u (W'.grow i).val).crest=((Typeface.brand X u i.val).crest).image ((Lace.project (h:=h) (H:=H) hC he).high.cut) ∧ ∀ V:Config G f, (Typeface.brand Y₁ u (W'.grow i).val).ingredient V=(Typeface.brand X u i.val).ingredient ((Lace.project (h:=h) (H:=H) hC he).high.links V)
   sector (i:↥b) : C'.supportP (Palette.sign (Typeface.brand X y) (stepped Q H) i.val)⊆ neighbors r x
   pillow i: i∈nearby C' K' x r n →
                (∃ j : Music C F, i=Mint.disc (stepped Q H) j ∧ W'.f i=Mint.disc (stepped Q h) (Deck.Stellar.verse_down (Lace.project (h:=h) (H:=H) hC he) j)∧verse R'.path j ≤ radiusB p) ∨
                 ∃ j' j₀:ℕ, i=Opacity.key (stepped Q H) j' ∧ W'.f i=Opacity.key (stepped Q h) j₀ ∧ (R.activities.reg j₀).support=((R'.activities.reg j').support).image ((Lace.project (h:=h) (H:=H) hC he).high.cut)∧
                  ∀ V:Config G f, Healthy R.p.threshold (R.activities.reg j₀).support V→R'.activities.E j' ((Lace.project (h:=h) (H:=H) hC he).high.links V)=R.activities.E j₀ V

variable (hc:2*(2*r+3)<c.val) (hz:Folding hC he C' c' X Y₁ y K' D' b b' x r n W')
include hc hz ht
lemma frosted : Boot X y C' b K' x r n c' Y₁ b' D' ((L).low.cut x) W':=by
   have hZ:(neighbors r x).image W'.halo= neighbors r (uₓ):=by rw [hz.largeSkin]; exact (inclined hC r x).symm
   have hp:c.val≤f.val:= h ▸ Nat.le_mul_of_pos_right _ P.L.property
   have hv:4<f.val:=by have h:=c'.laws.data.room.buys; omega
   have hu i (h:i∈hub X y C' b K' x r n): c'.supportP (W'.f i)=(C'.supportP i).image W'.halo := by
      rw [hz.largeSkin]; rcases Finset.mem_union.mp h with h|h
      · rcases hz.pillow _ h with ⟨i,h,h',hV⟩|⟨u,z,h,h',ht',hX⟩; · rw [h',h]; exact (Meadow.contempt hC he ht i).2
        rw [h',h]; exact mold hC he T T' (.logKey z) (.logKey u) (R:=R) (R':=R') ht' hv J.halo _
      obtain ⟨j,h',rfl⟩:=mem_image.mp h; rw [← (hz.memories ⟨_,h'⟩).1]; exact mold hC he T T' ((Y₁ _).wing) ((X _).wing) (R:=R) (R':=R') (hz.items ⟨_,h'⟩ y).1 hv J.halo _
   have hx':Boot X y C' b K' x r n c' Y₁ b' D' (uₓ) W':=by
      refine ⟨hz.signed,?_,fun i h=> let u := (hz.memories ⟨i,h⟩).2.choose; ⟨u,(hz.memories ⟨i,h⟩).2.choose_spec.1⟩, ?_,hZ,hz.largeSkin ▸ rfl,?_, hz.halos,?_,hz.sector,hu,fun i=>(hz.memories i).1⟩
      · intro i hi; obtain ⟨u,ht,h⟩:= (hz.memories (W'.grow.symm ⟨i,hi⟩)).2; rw [Equiv.apply_symm_apply] at h; exact h
      · rw [hz.largeSkin]; exact Meadow.garden hC x (by omega)
      · intro i hi j hj; rw [hz.largeSkin]; apply Deck.teaches; apply lt_of_le_of_lt ?_ hc; have he: separation i j ≤ _ := separation_triangle i x j; have hv:= (neighbors_mem ..).1 hi; have hp:= (neighbors_mem ..).1 hj; rw [separation_comm i x] at he; omega
      · intro i; let j:= W'.grow.symm i
        rw [show _= _ from ((congr_arg (fun i:↥b'=> Palette.sign Z₁ S i.val) (W'.grow.apply_symm_apply i)).symm.trans (hz.memories j).1)]
        rw [hu _ (Finset.mem_union_right _ (mem_image_of_mem _ j.2)),← hZ]; exact Finset.image_subset_image (hz.sector j)
   exact hx'

-- Peers for every localized output query along RELIABLE stencil.
local notation "U₀"=> words X y C' b K' r n x
local notation "U₁"=> words Y₁ y c' b' D' r n (uₓ)
variable (s:Sleet.Staff (Typeface.brand X y) C')(hp: Marvel X y C' b K' (k:=n) (r:=r) x s)
local notation "Δ₀"=> frosted hC he C' c' ht X Y₁ y K' D' b b' x r n W' hc hz
local notation "W₁"=> (Δ₀).flora s hp
-- lexical EXPOSURE
include hp
lemma peerTransit : Peers hC he C' c' X Y₁ y s (W₁):=by
    let D:=Δ₀
    refine ⟨s.1.fst,s.1.snd,(W₁).1.2,s.2,(W₁).2,rfl,rfl,fun i u=>?_⟩
    let v:=team (brand X u) (s.2 i); let v':=team (brand Y₁ u) ((W₁).snd i)
    let m:= (s.1.snd i).val; let m':=((W₁).1.snd i).val
    change Nonempty (Youth hC he v' v m m' (p:=p))
    have h₁: (s.2 i).reach = v.signs Y:= (Palette.label (brand X u) _).symm
    have h₂: ((W₁).snd i).reach= v'.signs S:= (Palette.label (brand Y₁ u) _).symm
    let A:= m\v.signs Y; let A':=m'\v'.signs S
    have hx : A'=A.image W'.f:= by unfold A A'; rw [← h₁,← h₂]; exact D.wearied s hp i
    have hw : A⊆ nearby C' K' x r n:= fun j hj=>by
        refine Finset.mem_filter.mpr ⟨hp.fair.paid i ?_, D.stock (manifested _ _ _ _ _ _ _ _ _ hp i ((mem_sdiff.mp hj).1))⟩; rw [h₁]; exact hj
    let e := Equiv.ofBijective (fun i:↥A=> (show ↥A' from ⟨W'.f i.val,by rw [hx]; exact mem_image_of_mem W'.f i.prop⟩)) (by
        refine ⟨fun i j hij=>Subtype.ext (hz.signed (show i.val∈hub X y C' b K' x r n from mem_union_left _ (hw i.prop)) (show j.val∈ _ from mem_union_left _ (hw j.prop)) (congr_arg Subtype.val hij)),fun i=>?_⟩
        obtain ⟨b,h,hp⟩:=mem_image.mp (show i.val∈A.image W'.f from hx ▸ i.prop); exact ⟨⟨b,h⟩,Subtype.ext hp⟩)
    let U := s.2 i; let U':=(W₁).snd i; let y' (j:↥U.val): ↥b := ⟨j.val,hp.fair.located i j.prop⟩
    let w (j:↥U.val) : ↥U'.val := ⟨(W'.grow (y' j)).val,(D.marks_reach s hp i _).mpr ⟨y' j,j.prop,rfl⟩⟩
    have hpW:Bijective w:=by
        refine ⟨fun i j h=>?_,fun k=>?_⟩
        · exact Subtype.ext (show (y' i).val=(y' j).val from congr_arg Subtype.val (W'.grow.injective (Subtype.ext (show (w i).val=(w j).val from congr_arg Subtype.val h))))
        obtain ⟨t,ht,hv⟩:= (D.marks_reach s hp i k.val).1 k.2; exact ⟨⟨t.val,ht⟩,Subtype.ext hv⟩
    have hg {ι:Type} {f c:Side} {R:RG.Rep G f} (p:ι→Leaf R) {S':StepData c f} (i: Drums p S'): Bijective (fun j:↥i.val=>show ↥(team p i).own from ⟨p j.val,Finset.mem_image_of_mem _ j.prop⟩):=by
       refine ⟨fun j k hk=>Subtype.ext (i.prop j.2 k.2 ?_), fun y=>?_⟩
       · exact congr_arg (fun a:Leaf R=>a.turn.badge S') (congr_arg Subtype.val hk)
       obtain ⟨x,h,hp⟩:= mem_image.mp y.2; exact ⟨⟨x,h⟩,Subtype.ext hp⟩
    let e':= Equiv.ofBijective _ (hg (brand X u) U); let d':= Equiv.ofBijective _ (hg (brand Y₁ u) U')
    let l:= e'.symm.trans ((Equiv.ofBijective w hpW).trans d'); have hl(j:↥U.val): l (e' j)=d' (w j):=by dsimp only [l,Equiv.trans_apply]; rw [Equiv.symm_apply_apply]; rfl
    refine ⟨e,(fun j=> hz.pillow j.val (hw j.2)), l, fun j Z=> ?_,fun j=>?_,fun j=>?_,h₁ ▸ hp.fair.valid i,h₂ ▸ (D.marvelous s hp).fair.valid i⟩
    · obtain ⟨k,rfl⟩:= e'.surjective j; rw [hl]; exact (hz.items (y' k) u).2 Z|>.symm
    · obtain ⟨k,rfl⟩:= e'.surjective j; rw [hl]; exact (hz.items (y' k) u).1
    obtain ⟨k,rfl⟩:= e'.surjective j; rw [hl]; exact (hz.memories (y' k)).2
end BoxOf
end YM.RemainderComparison.Seedlings
