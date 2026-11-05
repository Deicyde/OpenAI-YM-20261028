import YM.RG08.Vale.Longitude
/-!
# Call colors on every input site
-/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
noncomputable section
namespace YM.RG08.Vale
open RG Laurent Lattice Wilson Exterior Precision Bloch Push.AbsoluteSums Finset Function Filter Matrix Work.F08 Next.Free
open UVExt.Paths Stationary Planned.PrimaryIntegral295 Place Shade Quire Source Source.Drops Labels Scores Scores.Pages Tall
open scoped Topology ContDiff Classical BigOperators
variable {G:Gauge} {p m c f L:Side}{R:ℝ}{D d e j r n i k t:ℕ} {τ:ℕ}
variable {V W: BoardU D R G}
private lemma coin_basis' (s:G.El)(v: Link G p)(x: Body 1 p): arm G p 1 (stain s v) x= G.adjoint s (arm G p 1 v x) := by unfold stain; simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, (arm G p 1).apply_symm_apply]; rfl
private lemma shine (s:G.El)(x:Link G c)(M: Matrix (Body 1 f) (Body 1 c) ℝ): patron G M *ᵥ (stain s x)= stain s (patron G M *ᵥ x) := by
  have h (x:Link G c) (i:Body 1 f): arm G f 1 (patron G M *ᵥ x) i=∑ j:Body 1 c,M i j • arm G c 1 x j := by
    rcases i with ⟨i,j⟩; ext1 k
    rw [arm_apply, WithLp.ofLp_sum,Finset.sum_apply,tensor_same]
    exact congr_fun (FreeResolvent.component_mul M x k) (i,j)
  apply (arm G f 1).injective; funext i; rw [h,coin_basis',h,map_sum]; simp_rw [coin_basis', map_smul]

lemma halo_pay (g:Ratio c f) (i:Site c) (p:Site g.count)(A:Cross g.count (Loc G 1) (Loc G 1))(U:EnvelopeU D R G r)(ht:Tidy U)(φ:Exam D)(h:Whole A)(hz:Odd g.count.val)(hB:1/2≤R)(x: Link G c):
    rootSong (plug φ R∘halo p U A) c i x=rootSong (plug (roll (spinner p) (Carrier.unitStep g.count) φ) R ∘ U) f (g.assemble (i,p)) (installed g A*ᵥ x) := by
  rw [halo_one hz hB h ht]; exact belly_period g p h (Tidy.map _ ht) i _

structure Toute (U:EnvelopeU D R G r): Prop extends Tidy U where
  seatM : ∀ (m:Side)(φ:Exam D)(p:Site m), Stained G (rootSong (plug φ R ∘ U) m p)
lemma seat_made (h:Marvel τ V) : Toute (V i k) := by
  refine ⟨h.hem ..,fun m φ p=> ?_⟩
  let F i k:= plug φ R ∘ V i k
  change Stained G (rootSong (F i k) m p)
  by_cases ht:k≤τ+i; swap; · rw [show F i k=0 from not_ne_iff.mp (mt (Fits.echo h.cap φ i k) ht),root_zero]; exact fun _=>Eventually.of_forall fun x=>rfl
  let j:=τ+i-k
  obtain ⟨X,hX⟩:= Loom.shelved (n:=k+τ) (p:=j) (h.wardrobe m φ p) (by omega) (fun i k=>Tidy.map _ (h.hem i k))
  rw [← show Loom.strand τ j F k = F i k from by unfold Loom.strand j; rw [if_pos (by omega), show τ+i-k+k-τ=i by omega]]
  unfold rootSong; rw [← hX.scores_at k (by omega)]
  intro s 
  let T:= input G m; let U:= stain (m:=m) s; let c:= X ∘ T
  have ht : Tendsto T (𝓝 0) (𝓝 1):= by simpa [T] using input_cont.tendsto (0:Link G m)
  have he : Tendsto U (𝓝 0) (𝓝 0):= by simpa only [map_zero] using U.continuous.tendsto 0
  have hv : c ∘ U=ᶠ[𝓝 0] c := hX.coast T (T ∘ U) _ _ ht (ht.comp he) (.of_forall (fun x=> (stain_cons s x).symm))
  have hp:= ((hv.iteratedFDeriv ℝ k).eq_of_nhds); rw [Next.Foundations.jets_linear U (show ContDiffAt ℝ k c 0 from hX.hol.of_le le_top)] at hp
  exact Eventually.of_forall fun x => congr_arg ((k.factorial:ℝ)⁻¹ • · : ℝ→ℝ) (DFunLike.congr_fun hp (fun _=> x))

lemma paid_color {U:EnvelopeU D R G r}(h: Toute U)(A:Cross L (TypeFace 1) (TypeFace 1))(he:Whole A)(p:Site L)(hV:Odd L.val)(hp:1/2≤R): Toute (halo p U (painted G A)) := by
  have hz:Whole (painted G A) := by obtain ⟨w,C,hw,h⟩:=he; exact ⟨_,_,hw,paint_budget h⟩
  refine ⟨halo_tid hV hp h.toTidy hz,fun m g o i=>?_⟩
  let f:=m*L; let J:Ratio m f:=⟨L,rfl⟩; let P:= installed J A
  let x :(Link G m) →L[ℝ] Link G f:= (patron G P).mulVecLin.toContinuousLinearMap
  let v:=roll (spinner p) (Carrier.unitStep L) g
  have ht (U':Link G m): rootSong (plug g R ∘ halo p U (painted G A)) m o U'= rootSong (plug v R ∘U) f (J.assemble (o,p)) (x U') := by
    let B: Cross J.count (TypeFace 1) (TypeFace 1):=A; change rootSong (plug g R∘halo p U (painted G B)) m o _=_; rw [halo_pay J o _ (painted G B) U h.toTidy g hz hV hp U', paint_port]; rfl
  have hx : Tendsto x (𝓝 0) (𝓝 0) := by rw [← map_zero x]; exact x.continuous.tendsto _
  filter_upwards [hx.eventually (h.seatM f v _ i)] with y hy; dsimp only [Function.comp_apply]; rw [ht,ht,show x (stain i y)=_ from shine i y P]; exact hy
lemma tot_more {V U:EnvelopeU D R G r} (hv: Toute V)(hp:Toute U): Toute (V+U) := by
  refine ⟨hv.toTidy.plus hp.toTidy,fun m i j s=>?_⟩
  rw [show plug i R ∘ (V+U)= (plug i R ∘ V)+(plug i R ∘ U) from funext fun x=>map_add ..,rootSong,st_plus (hv.pens.shaped (plug i R)|>.of_norm) (hp.pens.shaped (plug i R)|>.of_norm)]; exact EventuallyEq.add (hv.seatM _ _ j s) (hp.seatM _ _ j s)
lemma tot_weight {U:EnvelopeU D R G r}(h:Toute U)(t:ℝ):Toute (t•U):= by
  refine ⟨h.toTidy.scale _,fun m i j s=>?_⟩
  rw [show plug i R ∘ (t•U)= t •(plug i R∘ U) from funext fun x=>by simp,rootSong,st_scale t (h.pens.shaped (plug i R)|>.of_norm)]; exact (h.seatM _ _ j s).mono fun i h=>congr_arg (t•·) h
lemma tot_less {V U:EnvelopeU D R G r}(hv:Toute V)(hp:Toute U): Toute (V-U):= by rw [sub_eq_add_neg,← neg_one_smul ℝ U]; exact tot_more hv (tot_weight hp _)
lemma tot_zero : Toute (0:EnvelopeU D R G r) := by refine ⟨Tidy.zero ..,fun m i j s=>?_⟩; rw [show plug i R ∘ (0:EnvelopeU D R G r)=(0:Shale _ _) from funext fun _=>map_zero _,root_zero]; exact Eventually.of_forall fun i=>rfl
lemma tot_sums {I:Type} {F:I→EnvelopeU D R G r}{s:Finset I}(h:∀ i∈s,Toute (F i)): Toute (∑ i∈s,F i) := by
  induction s using Finset.induction_on with
  | empty=> rw [sum_empty]; exact tot_zero
  | insert i s hi ih=> rw [sum_insert hi]; exact tot_more (h _ (mem_insert_self ..)) (ih fun k hk=> h _ (mem_insert_of_mem hk))
lemma dapple {U:EnvelopeU D R G r}(hv: Toute U)(φ: Exam D): Dappled (plug φ R ∘ U):= ⟨Tidy.map _ hv.toTidy, fun m=> hv.seatM m _ _⟩
end YM.RG08.Vale
