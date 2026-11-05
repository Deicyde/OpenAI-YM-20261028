import YM.RG08.Calendar.Tolls
import YM.RG08.Calendar.Actual
/-!
 # Joint prescription. Bind once when needing actual Floral in addition to the
 WilsonX formal terms. Technical detail on norms in e.g. Calendar/Way.
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
noncomputable section
namespace YM.RG08.Admission
open Function Filter Lattice Wilson Exterior Precision Laurent Finset RG Next.Free RG.Supply Bloch Input Conductor Wings Stationary Staffer Drift Virtue
open Town Run Quire Shade Loom Vale Needle Tall Planned.PrimaryIntegral295 Place Source Source.Drops Labels Summit Scores Door Creek Dart Wax Canon
open Next.Foundations UVExtension PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open ThroughLaunch
open scoped BigOperators Topology Real ContDiff Classical
variable {I J:Type} {G:Gauge}{K:KernelChoices} {F:Frames G}{p:Hol G}{Ω:∀ i,SectionData (F.level i)} {a:Ask} {P:Names G K}{b:Dialect p Ω P a}

-- Combine flexibly. all portals for this witness.
def treasury (D:ChartRatio G)(b:Dialect p Ω P a):Need:= (fast P D a.E a.vac).brings ((consents b).brings (skinT b))
variable {L:Levels G}{X:Names G L.clock.kernel}{w:Dialect p Ω X a}{D:ChartRatio G}{u:I→Windows}
lemma treasure (hp:G.Simple)(hD:LocalRatio D)(hs:∀ i,(Ω i).Sound p)(hv:∀ i,Bid.pop (Ω i))(hV:NearZ L u)(hP:∀ i,a.max_h+5≤ L.clock.J (u i).start)(he:∀ k, Affords (treasury D w) L (u k).start) (ν:G.ColorIndex):
    Ball X D ν u a.E a.vac ∧ Lights w u ν D ∧ Tincture w u := by
   have hx k:= (he k).of_sub (Need.Higher.back ..)
   have hB:= matters (ν:=ν) hV hp (fun i=> le_trans (Nat.le_add_left .. : 5 ≤ _) (hP i)) (fun i=> (he i).of_sub (Need.Higher.front ..))
   exact ⟨hB, loaded hs hv hp hD hV (fun i=> le_trans (by omega : a.max_h+2 ≤ a.max_h+5) (hP i)) (fun k=> (hx k).of_sub (Need.Higher.front ..)) hB, paths_in hp hV (fun i=> (hx i).of_sub (Need.Higher.back ..))⟩
structure Docks (C:Family G)(X:Names G C.path.levels.clock.kernel) where
   plan (a:Ask) : Dialect C.params C.localSection X a
   reserves a : ∀ᶠ i in atTop, Affords (treasury (chart G) (plan a)) C.path.levels i
   actual d: (C.localSection d).Sound C.params
   fields d: Bid.pop (C.localSection d)

-- discharge the whole Fixed-window setup just from Docks. Any eligible
-- I, over all starts above a, transfer history uniform. s can be ANY
-- period sequence consistent with subsequent Op application; `stepOp_uses`
-- matches on those.
lemma Docks.samples {C:Family G}(hG:G.Simple){X:Names G C.path.levels.clock.kernel}(W:Docks C X)(a:Ask) :
    ∀ᶠ k in atTop,∀ u:I→Windows,NearZ C.path.levels u →(∀ i,k ≤ (u i).start)→ ∀ ν:G.ColorIndex, Ball X (chart G) ν u a.E a.vac∧ Lights (W.plan a) u ν (chart G) ∧ Tincture (W.plan a) u:= by
  filter_upwards [W.reserves a, C.path.levels.fits.deep.eventually (eventually_ge_atTop (a.max_h+5))] with k hk hp u hu he ν
  exact treasure hG (chart_ok G) W.actual W.fields hu (fun i=> hp.trans (C.path.levels.fits.mono (he i))) (fun i=> hk.later (he i)) ν
lemma same_frames {F V:Frames G} {S:∀ i,SectionData (F.level i)}{S':∀ i,SectionData (V.level i)}{P P':Hol G}
    (h:F=V)(hp: HEq S S')(hv:P=P'){X:Levels G}{Q:Names G K}
    (Z:∀ i:Ask,Dialect P S Q i) :
   ∃ Z':∀ i:Ask,Dialect P' S' Q i, HEq Z Z' ∧ ∀ i D,treasury D (Z i) = treasury D (Z' i):= by
   subst V P'; obtain rfl:= eq_of_heq hp; exact ⟨_,HEq.rfl,fun _ _=> rfl⟩
lemma same_pop {F V:Frames G} {S:∀ i,SectionData (F.level i)}{S':∀ i,SectionData (V.level i)}(hv:F=V)(hp:HEq S S')(he:∀ i,Bid.pop (S i)) : ∀ i,Bid.pop (S' i):=by subst V; obtain rfl:=eq_of_heq hp; exact he

-- Any external indexed additional demands with these dependencies also supported
-- (can also use lower-level grants in minDelay/uv_wishes higher-up).
-- Kernel can be supplied before shot if needed.
set_option maxRecDepth 8000 in
theorem admits_one (h:G.Simple)(K:KernelChoices)(hp:∀ P:RG.Patch,P.Branches K G)[Encodable I](W:I→Need) : ∃ (C:Family G)(f:Extraction.Order)(T:Table C.book), Nonempty (Spec.Final C f T) ∧ C.Makes ∧ Spec.Calibrated C ∧ C.path.levels.clock.kernel=K ∧ Oasis.Floral (hG:=h) C ∧ (Extraction.Order.mk Extraction.Sequence.full f.per).Ordered C T ∧
   (∀ d k:ℕ,∀ᶠ p in atTop, ∀ n (v:Fin n→ C.book.Token), (∀ i,(v i).1 ≤ d)→ ∃ g,Poppy.Margins C n p k v g) ∧
   Bindage C ∧ (∀ i,∀ᶠ n in atTop,Affords (W i) C.path.levels n) ∧ ∃ N:Names G C.path.levels.clock.kernel,Nonempty (Docks C N):= by
   obtain ⟨N⟩:= names h K
   let B (a:Ask):= Classical.choice (wishes (Next.Foundations.sound G) (valuation G) N a)
   let V (i:I⊕ Ask):= Sum.elim W (fun a=> treasury (chart G) (B a)) i
   let v: Orders:= ⟨4,fun i=>6+i,fun i=>2+i,fun i=>100+i⟩
   have hE (i:ℕ): 100 ≤ v.supportExp i:= by change (100:ℝ) ≤ 100+i; simp
   have he : Draft v:= by
     refine ⟨le_rfl,fun i j hij=> Nat.add_le_add_left hij 6,fun i j hij=> Nat.add_le_add_left hij 2,fun i j hij=>?_,fun i=> lt_of_lt_of_le (by norm_num) (hE i),fun i=>by change _ ≤6+i; omega,fun i=>by change _≤2+i; omega⟩
     change (100:ℝ)+i≤100+j; gcongr
   obtain ⟨C,f,T,hZ,hC,hF,hX,H,x,hS,J,hB⟩:= oneC h K hp v he hE V
   have hV i:∀ᶠ n in atTop,Affords (V i) C.path.levels n:= (C.path.levels.fits.deep.eventually (eventually_ge_atTop (Encodable.encode i))).mono (fun j he=> hB _ j he)
   refine ⟨C,f,T,hZ,hC,hF,hS,hX,H,x,J,fun i=> hV (Sum.inl i),?_⟩
   subst K; obtain ⟨Z,-,hz⟩:= same_frames (X:=C.path.levels) J.fonts.symm J.stencil.symm J.parcel.symm B
   exact ⟨N,⟨Z,fun i=>by rw [← hz]; exact hV (Sum.inr i), hC.sections,same_pop J.fonts.symm J.stencil.symm (valuation G)⟩⟩

theorem sponsor (G:Gauge)(h:G.Simple)(γ:ℝ)(hγ:0<γ) : ∃ (C:Family G)(f:Extraction.Order)(T:Table C.book), Nonempty (Spec.Final C f T) ∧ C.Makes ∧ Spec.Calibrated C ∧ C.path.levels.clock.kernel.penalty=γ ∧ Oasis.Floral (hG:=h) C ∧ (Extraction.Order.mk Extraction.Sequence.full f.per).Ordered C T ∧
   (∀ d k:ℕ,∀ᶠ p in atTop, ∀ n (v:Fin n→ C.book.Token), (∀ i,(v i).1 ≤ d)→ ∃ g,Poppy.Margins C n p k v g) ∧
   Bindage C ∧ ∃ N:Names G C.path.levels.clock.kernel,Nonempty (Docks C N):=by
    obtain ⟨K,hK,H⟩:=Axial.viable G γ hγ
    obtain ⟨C,f,T,hF,hM,hC,hP,hv,hZ,H,Z,-,V⟩:= admits_one h K H (fun i:Empty=>i.elim)
    exact ⟨C,f,T,hF,hM,hC,hP ▸ hK,hv,hZ,H,Z,V⟩
end YM.RG08.Admission
