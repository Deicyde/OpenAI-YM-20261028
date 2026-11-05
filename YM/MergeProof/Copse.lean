import YM.MergeProof.Close
import YM.MergeProof.Plaza
import YM.MultiNext.VACUUM_STABILITY.Localized.Cascade
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Menu
open Function Filter Lattice Wilson RG MeasureTheory Finset Push Local Extra.Histories PhysicalNext.Repeat Lotus Merge Merge.Palette Accent Marker
open Extra.Multi GridApprox.Nil
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {V ι β : Type}[DecidableEq V] {B:Census V} {G:Gauge}{f c:Side}{R:Rep G f}{E:Rep G c}
open Extra.Trajectories Planned.GuardedAtom
variable [Fintype V][Fintype ι]
    {D:GaugeDoor R E}{S:StepData c f}
    {w:V→ℝ} {A C p v W S' ζ d u: ℝ}{o:V→Site f}{b:V→Site c}
structure Canopy (S: StepData c f) (H:GaugeDoor R E) (o:V→Site c)(r:V→ℝ)(z y s v:ℝ)(q:ι→Hat B R): Prop where
   buyer : ∃ (F:Support c→ Config G c→ Poly B)(K:Box c→ Config G c→Poly B), Towed r id F E.p.B z s ∧ (∀ i,Burns o i (F i) E.p.threshold) ∧ Towed r Prod.fst K E.p.B y v ∧ (∀ i,Flow o i (K i) E.p.threshold) ∧
      S.push R.beta (Expense q r S)=play E B K (fun U=>∑ i,F i U) ∧ (∀ i U,(K i U).part B.quiet=profile E.activities (fun j=> Complex.ofReal ∘ E.activities.K j) i U)∧
        ∀ i U j,(K i U).part (B.fire j)= ∑ l,owl (q l) H j i U
-- push eq issue StepData.A includes Op.
structure Volant (S:StepData c f)(D:GaugeDoor R E)(N:ℕ) (d c' v y w b:ℝ):Prop where
   reserves {V:Type} [DecidableEq V] [Fintype V] {ι:Type} [Fintype ι]{o:V→Site f} {r:V→ℝ}{B:Census V}: ∀ q:ι→ Hat B R, (∀ i,0<r i)→Occupancy (S.ratio.parent ∘ o) N→ Offer o q r R.p.B d c'→ Canopy S D (S.ratio.parent ∘ o) r v y w b q
   propagate: SoundDoor S D
   tunes: Tunes D
   contact: Arsenal R
-- Mono. absorption integration.
omit [Fintype V] [Fintype ι] in
lemma Offer.fatten {q:ι→Hat B R}(he:Offer o q w R.p.B d v)(h:v≤p):Offer o q w R.p.B d p := ⟨he.sites,fun i=>⟨(he.budget i).1,(he.budget i).2.1,(he.budget i).2.2.trans h⟩⟩
-- Using real-C norm via finiteDim. need Poly EndContinuousReal. import. integration rules.
omit [Fintype V] in
lemma heat (q:ι→Hat B R)(S:StepData c f)(w:V→ℝ){σ C t e c':ℝ}(hg:R.Lawful σ C t e c'):
    Integrable (Expense q w S) (prior G f):=by
   unfold Expense Merge.Photo.given
   refine integrable_finsetSum _ fun i _=>?_ ;
   -- smul complex Poly; real to complex measurable etc.
   exact ((((((team _ i).sells hg).1.integrable _).mul_const _)).smul_const _) -- use real
omit [Fintype V] in
lemma convective (S:StepData c f) {Y: Config G f→Poly B} (f:Poly B) (β:ℝ) (hK:S.IsKernel β G)(hY:Integrable Y (prior G _)) (U:Config G c) : S.push β (fun i=> f*Y i) U=f* S.push β Y U:=by
   let L : Poly B →ₗ[ℂ] Poly B :={ 
                                    toFun:= (f*·)
                                    map_add':= fun a b=>mul_add ..
                                    map_smul':=fun a b=> mul_smul_comm .. }
   have hp:= StepData.push_slice hK U Y hY
   let p:Poly B→ₗ[ℝ] Poly B:= L.restrictScalars ℝ
   let T:= p.toContinuousLinearMap
   unfold StepData.push; simp_rw [← mul_smul_comm]; exact ContinuousLinearMap.integral_comp_comm T hp
variable {σ C t e c' M x η k a b' q g u₀ δ τ z' :ℝ} {N m:ℕ}
variable {X : Config G f→ Poly B} {ν:V→ℂ}{L:V→ Config G f→ℂ}{κ: Specialty G f V} {L':V→ Config G c→ℂ}{K':V→ ℕ→ Config G c→ℂ}
    {v':V→ℝ}
local notation "X₀" => S.push R.beta X
omit [Fintype ι] in
lemma stroke (h:Volant S D N d M (t+η) p k u)(hv:∀ i,0<w i)(hV:∀ i,0<v' i) (hr:R.Lawful σ C x τ b')(hx:0 ≤ d)(he:d+1 ≤ R.p.supportExponent)(hg:E.activities.Valid E.p δ z')
    (hX:Served R L κ X o w d q)(ht':∀ U i,(S.push R.beta X U).part (B.fire i)=coin E (L' i) (K' i) U) (hc':∀ i,Dominated (K' i))
    {y n: V→ℝ}(hp:∀ i,∃ Z:Set Wing,Z.Finite∧Tale Z (o i) (S.ratio.parent (o i)) 1 (L i) (κ i) (profile E.activities (K' i)) (ν i) (y i) (n i) D)
    (hm:Occupancy o m)(hs:Occupancy (S.ratio.parent ∘ o) N)
    (hA:0 ≤ c')(hh:∀ i,2*w i*y i≤ c')(hh':let T:= m*siteFactor R.p.B*c'+4*q; T+Real.exp T*T≤ M)
    (hh0:∀ i,w i*n i ≤ W)(hW:0≤ W)(hf:p+1 ≤ E.p.supportExponent+2)
    (ht:0 ≤ t+η)(hF:((E.p.B+E.p.B+1:ℕ):ℝ)^4 * (u+N*siteFactor E.p.B *W) ≤ p-(t+η))
    (hG:Repegs (S.ratio.parent ∘ o) E.p.B w v' η a B)(ha:0≤a)(hc:a*k≤g)(hy:a*(Real.exp (u+N*siteFactor E.p.B*W)-1) ≤ g)
    (hZ:S.IsKernel R.beta G)(hit:∀ U,E.eval U≠0): Served E L' (fun i=>profile E.activities (K' i)) (S.push R.beta X) (S.ratio.parent ∘ o) v' t g:=by
   obtain ⟨I,i,Q,H,ψ,hψ,hp,hq⟩:= inventory hv h.contact h.tunes h.propagate hr hX hx he hp hm hA hh hh0 hf
   obtain ⟨F,K,hT,hU,hB,hM,hY,hP,hL⟩:= (h.reserves Q hv hs (H.fatten hh')).buyer
   let s:=Mach B ν; let b:= fun U=>∑ i,F i U; let f' U:= s+b U
   have htU: S.push R.beta X=play E B K f' :=by
      funext U; rw [show X=(fun U=>_) from funext hq,convective S _ _ hZ (heat Q S w hr),hY];
      unfold play f'; rw [pass_add (mute B ν) (show (b U).part B.quiet=0 from ?_), mul_smul_comm];
      · unfold b; rw [mul_assoc]
      unfold b; rw [Poly.part_sum]; exact Finset.sum_eq_zero (fun j _=> (hU j).sil U)
   rw [htU]; refine closeup E ψ K f' (B:=B) hψ hM hP hg (a:=a) ?_ ?_ hv hW hs hU hT hB ?_ ht hF hV hG ha hc hy ?_ (fun i U=> htU ▸ ht' U i) hc' hit -- duplicate fields etc
   · intro U; unfold f'; rw [Poly.part_plus,mute];unfold b; rw [Poly.part_sum]; simp_rw [show ∀ i,(F i U).part B.quiet=0 from (fun i=>(hU i).sil U),sum_const_zero,add_zero]
   · intro U p hp; unfold f'; rw [Poly.part_plus,hush _ _ hp,zero_add]
   · ring
   intro p i U; rw [hL]; exact (congr_fun (hp i p) U).symm
end YM.MergeProof.Menu
