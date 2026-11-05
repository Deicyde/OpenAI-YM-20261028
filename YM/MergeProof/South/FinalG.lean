import YM.MergeProof.South.Dine


/-!
 # coalescence close in honest `late` (and even uniformly here). real projection. furnishes the actual Grill.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Accent
open Finset Function Filter MeasureTheory Lattice Wilson RG Push Marker Source Extra.Histories
open Planned.GuardedAtom Next.Rank Edition Spindle Extra.Multi Motion Local Bid Cells Extraction Exponential Overlay
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
open GridApprox.Joint GridApprox
variable {V:Type}[Fintype V][DecidableEq V]{B:Census V} {G:Gauge}(C:Family G)(N k m p d:ℕ)(H:C.Makes)
variable {W:Worth}{u ψ φ δ:ℕ→ℝ}{r:ℕ→ℕ}{ζ:ℕ→ℕ→ℝ}{D:∀ N p m:ℕ,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
variable (w:ℝ){j:ℕ}
set_option quotPrecheck false
open Relay
local notation "T"=> C.path
local notation "ℓ"=> C.ref d
local notation "F"=> C.labels.level d
local notation "Y!"=> C.localSection d
local notation "a!"=> C.S.a
local notation "s!"=> C.factory d N p
local notation "R"=> C.path.rep N p
variable (L:C.label d) (hr:star L=L)
local notation "ζ!"=> ζ d
variable (h:Scrim C W u ψ φ δ ζ r D) {f:Extraction.Order} (J:ℕ) (K:Stock.Tabs C.path.levels) {ε α:ℝ}
open Next.UVStress
-- origin basis directly
local notation "U"=> C.O N p L 0
include H hr
section
variable (U':Config G (C.side N p)→ℂ)
lemma realityC (hk : J ≤ N) (hc : C.ref d ≤ N) (hα:∀ x, ‖U' x‖ ≤ α) (hH:Interior ((center C.S p hk 0).chamber 0) U) (hY:Interior ((center C.S p hk 0).chamber 0) U') (ht : (center C.S p hk 0).rootTest (C.beta N p) (U'-U) ≤ ε) : ∃ V':Config G (C.side N p)→ ℝ, (∀ x,|V' x| ≤ α)∧ Interior ((center C.S p hk 0).chamber 0) (Next.UVStress.paint V') ∧ (center C.S p hk 0).rootTest (C.beta N p) (Next.UVStress.paint V'-U) ≤ ε:=by
   let t:= center C.S p hk 0; let s:=(1/2:ℂ); let a x:ℝ:=(U' x).re; let K:= t.chamber 0; let Z:= U; let C':= C.beta N p; have hX: star Z=Z:=funext fun x=>by change star (Z x)= Z x; unfold Z; rw [← C.reality H hc _ 0 x,hr]
   have he : Next.UVStress.paint a = s • U' + s • (star U'):=by funext x; unfold a Next.UVStress.paint s; simp only [Pi.add_apply,Pi.smul_apply, Pi.star_apply,smul_eq_mul]; apply Complex.ext <;> simp <;> ring -- real calc
   refine ⟨a,fun x=> (Complex.abs_re_le_norm (U' x)).trans (hα x), by rw [he]; exact (hY.scale _).plus (hY.real.scale _),?_⟩
   let w:=U'-Z; have hp: Interior K w:= Next.UVStress.minus hY hH
   have hh : Next.UVStress.paint a-Z = s • w + s • (star w):=by
                                                     rw [he]; unfold w; rw [star_sub,hX]; have hv : s • Z+s • Z=Z:=by rw [← add_smul,show s+s=1 from by unfold s; ring,one_smul]
                                                     rw [smul_sub,smul_sub]; nth_rw 1 [← hv]; abel
   have hs := (seamless H N p).semi t (s • w) (s • star w) (hp.scale s) (hp.real.scale s)
   rw [hh]; refine hs.trans ?_; have hm: t.rootTest C' (star w)= t.rootTest C' w:= Work.B15.rootTest_star t C' w
   rw [Next.Extract.root_smul,Next.Extract.root_smul,hm, show ‖s‖=(1:ℝ)/2 by simp [s,norm_div]]; linarith only [ht]
end
include h K
lemma inTime (hV : Stock.Tabs.opens C.path.levels 1 J m)(hK : ℓ ≤ m)(he:0 < ε) : ∃ B A, Origin C f J ⟨d,L⟩ ε B A:=by
   let Q i:= (C.path.levels.params i).columns
   let b i:= ‖alto T m d‖*(4*(1+Q i)/gainChart T i m); let s:= stakes C J m; let w i:ℝ:= ζ d m/2/b i
   have hv i:0 < b i:=by unfold b; rw [alto_norm]; have hz:0 < C.S.a m:= C.S.a_pos m; have hh:1 ≤ Q i:= (C.path.levels.params i).columns_ge; have ht:0 < Q i:=zero_lt_one.trans_le hh; have ho:0<gainChart T i m:= Real.exp_pos _; exact mul_pos (inv_pos.mpr (pow_pos hz _)) (div_pos (by positivity) ho)
   have hh : 0 < ζ d m:= h.grows d m hK; have hw i : 0 < w i:= div_pos (by positivity) (hv i)
   have ht : ∀ᶠ i:ℕ in atTop, stockK C i d L * (s/w i) ≤ ε:=by
      -- lift subseq ident.mesh using Order persistence. Simpler levy. use identity Order.
      let F':= Extraction.Order.full
      let a i:= stockK C i d L * s * (ζ d m/2)⁻¹
      let l i:= 4*(1+Q i)
      let v i:= ‖alto T m d‖* l i*Real.exp (Push.RelayDifference.gamma*C.S.scale m)
      have hD(i:ℕ): stockK C i d L*(s/w i)=a i*v i*RelayDifference.flight C (-RelayDifference.gamma) (i,0):=by
         unfold w; rw [div_div_eq_mul_div]; unfold b a v RelayDifference.gamma RelayDifference.flight l gainChart; rw [mul_sub,Real.exp_sub,div_div_eq_mul_div,neg_mul,Real.exp_neg]; dsimp only [Family.S]; ring_nf; simp only [inv_inv]; ring -- negative convert edit
      have hX : RelayDifference.Slow C F' (fun i=> Real.exp (Work.D01.columnLogs (T).levels i.1)):=by
         intro ε he; filter_upwards [(RelayDifference.cutoff_grows F').eventually (Work.D01.columnLogs_le (T).levels ε he)] with i hx; exact ((Real.norm_of_nonneg (Real.exp_pos _).le).le.trans (Real.exp_monotone hx): ‖Real.exp (Work.D01.columnLogs (T).levels i.1)‖ ≤ _)
      have hI: RelayDifference.Slow C F' (fun i=>a i.1):= ((((RelayDifference.Slow.const (C:=C) _).mul hX).mul (RelayDifference.Slow.const _)).mul (RelayDifference.Slow.const _)).mul (RelayDifference.Slow.const _)
      have hz₀: RelayDifference.Slow C F' (fun i=> l i.1):= (RelayDifference.Slow.const (C:=C) (4:ℝ)).mul ((RelayDifference.Slow.const (C:=C) 1).add (RelayDifference.columns_slow (C:=C) (f:=F')))
      have hz: RelayDifference.Slow C F' (fun i=>v i.1):=((RelayDifference.Slow.const (C:=C) _).mul hz₀).mul (RelayDifference.Slow.const (C:=C) _) 
      have h₀: ∀ᶠ i in F'.fuse, stockK C i.1 d L * (s/w i.1) ≤ ε:=by
         filter_upwards [(hI.mul hz).sink (a:=1/16) (b:=RelayDifference.gamma) (by unfold RelayDifference.gamma; norm_num), (RelayDifference.flight_lands (ε:=1/16) (C:=C) (f:=F') (by norm_num)).eventually (ge_mem_nhds he)] with i h h'; rw [hD]; exact h.trans h'
      rw [Extraction.Order.fused] at h₀; exact h₀.exists.choose_spec
   obtain ⟨i,hk,hε,hM⟩:= ((eventually_ge_atTop m).and (ht.and (plenty C.path.levels J (lensScope C d)))).exists
   obtain ⟨A,hA,ht⟩:= dine C i m d H (w i) L h J K hV hK hk (hw _) hM (by rw [mul_assoc]; exact le_of_eq (div_mul_cancel₀ _ (hv _).ne'))
   have hu := fun N p=> fun hi:i<N=>fun hx: ∀ (v:C.label d), Interior ((center C.S p (hV.1.trans (hk.trans hi.le)) 0).chamber 0) (C.O N p v 0)=> ht N p hi (hV.1.trans (hk.trans hi.le)) hx
   have hp(N p):∀ h:i<N, let z:=hV.1.trans (hk.trans h.le); (∀ (v:C.label d), Interior ((center C.S p z 0).chamber 0) (C.O N p v 0)) → ∃ B:Config G (C.side N p)→ℝ,(∀ x, |B x| ≤ A) ∧ Interior ((center C.S p z 0).chamber 0) (Next.UVStress.paint B) ∧ (center C.S p z 0).rootTest (C.beta N p) (Next.UVStress.paint B-C.O N p L 0) ≤ ε:=by
      intro hi z hf; obtain ⟨B,hH,hT,hσ⟩:=hu N p hi hf; exact realityC C N p d H L hr J _ z (hK.trans (hk.trans hi.le)) hH (hf L) hT (hσ.trans hε)
   choose! Z hZ using hp; refine ⟨Z,A,hA,?_⟩; unfold Extraction.Order.late; filter_upwards with k; filter_upwards [f.mesh.cofinal.eventually_gt_atTop i, f.mesh.cofinal.eventually (Stock.clear_interior C H J d)] with j hi hj; exact ⟨hj.1, hZ _ (f.per k) hi (hj.choose_spec _ _)⟩
omit hr
lemma grilled (hs:CellHyp C f) : Org.Grill C f:=by
    intro d m
    let n:=max m ((Finset.range (d+1)).sup (fun i=> C.ref i)); have hk(i:ℕ)(hi:i≤d): C.ref i ≤ n:=(Finset.le_sup (f:=fun j=> C.ref j) (Finset.mem_range.mpr (by omega))).trans (le_max_right ..)
    let p:= Stock.Tabs.chosen C.path.levels 1 K n; have hp : Stock.Tabs.opens C.path.levels 1 n p:= Stock.Tabs.opened ..
    have he(i:ℕ)(v:Next.UVStress.Entitled C d):∃ B A, Origin C f n v.val (costHint i) B A:= by
       obtain ⟨⟨j,z⟩,ht,hv⟩:= v; exact inTime C p j H z hv h n K hp ((hk j ht).trans hp.1) (cost_pos i)
    choose B A hA using he
    exact ⟨n,le_max_left ..,fun _ v hv' h' => Next.UVStress.Maker.patrons (show Next.UVStress.Maker C f n d from ⟨B,A,hA⟩) H hs v hv' h'⟩
end YM.MergeProof.Accent
