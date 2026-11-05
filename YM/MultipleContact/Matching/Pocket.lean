import YM.MultipleContact.Matching.Twirls
import YM.MultipleContact.Fields

/-! Transfer of the unselected pair bounds to all fixed compact exterior configurations and physical labels. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.MultipleContact.Local
open Filter Function MeasureTheory Analysis Extraction Table Ward MergeProof Acme Ribbons Around Cells Wilson Lattice Climb Set Metric
open Matching
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {G:Gauge}{C:Family G}{S:Table C.book}{F:Extraction.Order}{W:DiffPlan S} {D:ℕ}
variable {ι:Type*}[Fintype ι]{n:ι→ℕ}
variable {X:S.Rotation}
private def lit (R:Ortho)(q:C.book.Token):C.book.Token:=expose (X.label R (S.classTokens q))
private lemma lit_apply {X:S.Rotation} (R:Ortho)(q:C.book.Token):S.classTokens (lit (X:=X) R q)=X.label R (S.classTokens q):=by
      dsimp only [lit,expose,Rotation.label,classTokens]; congr 1;exact (S.rep ..)
omit [Fintype ι] in
private lemma continuous_move_val (R:Ortho)(u:ι):Continuous (fun z:Points (n u) => Points.move R z):=by
    unfold Points.move points
    exact (PiLp.continuous_toLp _ _).comp (continuous_pi fun i=> (Ortho.motion R).continuous.comp (show Continuous (fun x:Points _=>x i) from by fun_prop))
private def repack (R:Ortho)(z:∀i,Points (n i)):=fun i=>Points.move R (z i)
private lemma continuous_repack (R:Ortho) : Continuous (repack (n:=n) R):=continuous_pi fun i=> (continuous_move_val R i).comp (continuous_apply i)
omit [Fintype ι] in
lemma carries {n':ℕ}(R:Ortho)(y:E4)(z:Points n'):Points.move R (Points.cons y z)=Points.cons (Ortho.move R y) (Points.move R z):=by ext1 i; exact Fin.cases rfl (fun j=>rfl) i

variable (ρ:S.RealSpin)(hx:X.Laws W ρ)(hO:X.Oriented S)
include hO
omit [Fintype ι] in
lemma rot_once {n':ℕ}(R:Ortho)(v:S.Tag)(q:Fin n'→ C.book.Token)(z:Points n')(he:Points.cons 0 z∈conf _): once q v z=once (lit (X:=X) R∘q) (X.label R v) (Points.move R z):=by
      have hx:= hO _ (Fin.cons (α:=fun _=>S.Tag) v (S.classTokens∘q)) (Points.cons 0 z) he R
      rw [carries,show R.move 0=0 from (R.motion).map_zero,Work.A01.comp_cons] at hx
      unfold once disc; rw [hx.symm]
      congr 2
      ext1 j
      exact (lit_apply ..).symm

omit [Fintype ι] in
lemma rot_pair {n':ℕ}(R:Ortho)(V B:S.Tag)(q:Fin n'→ C.book.Token)(y:E4)(z:Points n')(he:Points.cons y (Points.cons 0 z)∈conf _): twice q V B y z=twice (lit (X:=X) R∘q) (X.label R V) (X.label R B) (R.move y) (Points.move R z):=by
      have hx:= hO _ (Fin.cons (α:=fun _=>S.Tag) V (Fin.cons B (S.classTokens∘q))) _ he R
      rw [carries,carries,show R.move 0=0 from R.motion.map_zero,Work.A01.comp_cons,Work.A01.comp_cons] at hx
      unfold twice disc; rw [hx.symm]; congr 1; funext i; refine Fin.cases rfl (fun j=>Fin.cases rfl (fun k=>(lit_apply ..).symm) j) i

omit hO
variable (q:∀i:ι,Fin (n i)→ C.book.Token)(V B:S.Tag)(o:Option ℕ)(ε:ℝ)
private def ok (S:Table C.book) (z:∀i,Points (n i)) (c:ι→ℂ):Prop:=match o with | none=> True | some n=> silent q S n z c
private def power :ℝ:= -(B.1:ℝ)-V.1 + match o with | none => -ε | some n => (n+1/64)
variable (K:Set ((i:ι)→Points (n i)))(hK:IsCompact K)(hsafe:∀x∈K,∀i, Points.cons 0 (x i) ∈ conf (n i+1))
variable (hT:Acme.Aroma C)(hh:Matching C)
variable (hm:W.Derivatives S)(hc:S.Hierarchy)(hp:F.PointLimits C S)(hq:Cells.CellHyp C F)(hC:C.Makes)(hG:G.Simple)
include hK hsafe hO
private lemma supportT {u:ℝ}(R:Ortho)
   (he:predicate ((repack R)''K) (fun i=>lit (X:=X) R ∘ q i) (X.label R V) (X.label R B) (ok (fun i=>lit (X:=X) R∘q i) o S) (power (X.label R V) (X.label R B) o ε)):
     predicate K q V B (ok q o S) (power V B o ε):=by
     let K':= repack R ''K
     obtain ⟨r,hr,hyo⟩:=he; obtain ⟨δ,hδ,hgap⟩:=gapK K hK hsafe
     refine ⟨min δ r,lt_min hδ hr,fun z hz c hm hy y hy' hq=>?_⟩
     have hc(i):Points.cons y (Points.cons 0 (z i))∈conf _ :=by
         have hf:(min δ r)≤ δ:=min_le_left ..
         have he' (j:Fin (n i+1)): y ≠ Points.cons 0 (z i) j:=by
                      intro hne
                      refine Fin.cases (?_) (fun j he=>?_) j hne
                      · intro hne; change y=0 at hne; rw [hne,norm_zero] at hy'; linarith
                      have ht:= hgap z hz i j.succ 0 (Fin.succ_ne_zero _); refine hq.not_ge (?_); suffices hv:δ < ‖y‖ from hv.le.trans' hf;  change _ < ‖Points.cons 0 (z i) j.succ-(Points.cons 0 (z i) 0)‖ at ht; rw [← he,show Points.cons 0 (z i) 0=0 from rfl,sub_zero] at ht; simpa using ht -- reverse
         show Injective _;intro j k
         refine Fin.cases (?_) (fun x=>?_) j
         · exact Fin.cases (fun _=>rfl) (fun _ h=>(he' _ h).elim) k
         exact Fin.cases (fun h=>(he' x h.symm).elim) (fun l h=>congr_arg Fin.succ (hsafe z hz i h)) k
     

     let u:= R.move y; have hu : ‖u‖=‖y‖:= R.move_norm _
     have hZ : ok (fun i=>lit (X:=X) R∘q i) o S (repack R z) c:= by
          cases o with
          | none=>trivial
          | some D => intro v
                      have hv: v = X.act D R ((X.act D R).symm v) := ((X.act D R).apply_symm_apply _).symm
                      have hs:=hy ((X.act D R).symm v)
                      rw [hv];exact Eq.trans (Finset.sum_congr rfl fun i _=> congr_arg (c i * ·) (Eq.symm (rot_once hO R ⟨D,_⟩ (q i) (z i) (hsafe z hz i)))) hs
     have h := hyo (repack R z) ⟨z,hz,rfl⟩ c hm hZ u (hu ▸ hy') ((lt_of_le_of_lt hu.le hq).trans_le (min_le_right ..))
     rw [hu] at h
     change _ ≤ ‖y‖^power V B o ε at h
     exact (congr_arg (‖·‖) (Finset.sum_congr rfl fun i (_:i∈(Finset.univ:Finset ι))=>congr_arg (c i * ·) (rot_pair hO R V B (q i) y (z i) (hc i)))).le.trans h

include hm hc hp hq hC hG hT hh
private lemma pocket (hε:0<ε)(z:((i:ι)→Points (n i))) (hz:z∈K):∃ U∈𝓝 z,predicate (K∩ U) q V B (ok q o S) (power V B o ε):=by
    obtain ⟨δ,hδ,hp'⟩:=gapK K hK hsafe
    obtain ⟨p,hh'⟩ := (((C.S.shrinks.const_mul 4).eventually (gt_mem_nhds (show 4*(0:ℝ)<δ by rwa [mul_zero]))).exists)
    obtain ⟨R,ℓ,hR⟩:=safe_rotation z C p
    let s:=C.S.a p; have ht':0<s:=C.S.a_pos _
    have hA : ∃ ε> (0:ℝ), ∀ i,Locations C p ε (ℓ i) (Points.move R (z i)):=by
        have hp (i)(k:Fin (n i))(j:Axis):∀ᶠ ε in 𝓝 (0:ℝ), |Points.move R (z i) k j - C.S.gridPoint p (ℓ i k) j| < s/2-ε :=by
            set w:= |Points.move R (z i) k j - C.S.gridPoint p (ℓ i k) j|
            have hw:=hR i k j; change w<s/2-0 at hw; exact (filter_mono_lt hw)
        exact ((show ∀ᶠ ε:ℝ in 𝓝[>] (0:ℝ),0<ε from self_mem_nhdsWithin).and ((eventually_all.mpr fun i=>eventually_all.mpr fun k=>eventually_all.mpr fun j=>hp i k j).filter_mono nhdsWithin_le_nhds)).exists
    obtain ⟨δ',hδ',hQ⟩:= hA
    let xg(i) := Points.move R (Points.cons 0 (z i))
    let yg(i):=Fin.cons (α:=fun _=>Cover) 0 (ℓ i)
    have he₀(i):xg i = Points.cons 0 (Points.move R (z i)):= (carries ..).trans (congr_arg (Points.cons · _) (R.motion.map_zero))
    have he (i)(j:Fin (n i+1))(a:Axis):|xg i j a-C.S.gridPoint p (yg i j) a|<s/2:= (by
        rw [he₀]
        exact Fin.cases (by simpa [Points.cons,yg,Schedule.gridPoint] using (half_pos ht')) (fun j=>(hQ i j a).trans (by dsimp [s]; linarith only [hδ'])) j)
    have hInd(i):Injective (yg i):=by
       intro j k hy; by_contra h₀
       obtain ⟨a,ha⟩:=above_coord s (xg i k-xg i j) ((show 4*s <δ from hh').trans (by
           change δ < ‖R.motion _-R.motion _‖; rw [← map_sub,R.motion.norm_map]; exact hp' z hz i k j (Ne.symm h₀)))
       change s < |xg i k a-xg i j a| at ha; have h₁:=he i j a; rw [hy] at h₁; exact ha.not_gt ((abs_sub_lt_iff).mpr (by rcases abs_sub_lt_iff.mp h₁ with ⟨h1,h2⟩; rcases abs_sub_lt_iff.mp (he i k a) with ⟨h3,h4⟩; constructor <;> linarith only [h1,h2,h3,h4]))
    let f(x) := repack (n:=n) R x
    have hw(i k a):∀ᶠ x in 𝓝 z, |f x i k a - C.S.gridPoint p (ℓ i k) a| < s/2-δ' :=((show Continuous (fun x=>f x i k a) from by unfold f repack; have := continuous_move_val (n:=n) R i |>.comp (continuous_apply (A:=fun i=> Points (n i)) i); exact ((show Continuous (fun x:Points (n i)=>x k a) from by fun_prop).comp this)) |>.sub continuous_const |>.abs |>.tendsto z).eventually (gt_mem_nhds (hQ ..))
    obtain ⟨c,hc',H⟩:=Metric.mem_nhds_iff.mp (show ∀ᶠ x' in 𝓝 z, ∀i k a, |f x' i k a - C.S.gridPoint p (ℓ i k) a| < s/2 - δ' from eventually_all.mpr fun i=>eventually_all.mpr fun k=> eventually_all.mpr fun a=>hw i k a)
    let A:=K ∩ closedBall z (c/2)
    let K' : Set ((i:ι)→Points (n i)):= f '' A
    have hL: IsCompact A:=hK.of_isClosed_subset (hK.isClosed.inter Metric.isClosed_closedBall) Set.inter_subset_left
    have hL':IsCompact K':=hL.image (continuous_repack ..)
    have he(z')(hz:z'∈A):∀i,Locations C p δ' (ℓ i) (f z' i):= H (closedBall_subset_ball (half_lt_self hc') hz.2)
    have hh' : ∀ z∈K',∀i, Points.cons 0 (z i)∈conf (n i+1):=by
         rintro z' ⟨y,hy,rfl⟩ i
         rw [show Points.cons 0 (f y i)=Points.move R (Points.cons 0 (y i)) from ((carries R ..).trans (congr_arg (Points.cons · _) R.motion.map_zero)).symm]
         exact Points.move_in R (hsafe _ hy.1 i)
    let q' (i) := lit (X:=X) R∘q i
    have hq' : ∀ z∈K',∀i, Locations C p δ' (ℓ i) (z i):=by rintro i ⟨y,hy,eq⟩; rw [← eq]; exact he y hy
    refine ⟨closedBall z (c/2), closedBall_mem_nhds _ (half_pos hc'), ?_⟩
    apply supportT (u:=ε) hO q V B o ε A hL (fun z hz i=>hsafe _ hz.1 i) R
    rcases o with _|D
    · refine Eq.mp (show predicate K' q' (X.label R V) (X.label R B) _ _ = predicate K' q' (X.label R V) (X.label R B) (fun x y=>True) (power (X.label R V) (X.label R B) none ε) from congr_arg (predicate K' q' (X.label R V) (X.label R B) (fun x y=>True)) (show _=_ from ?_)) (unconditionedNear hG K' hL' hh' hT hh q' (X.label R V) (X.label R B) hc hp hq hC hm ℓ hInd hq' hδ' ε hε)
      unfold power; ring
    refine Eq.mp ?_ (signedNear hG K' hL' hh' hT hh q' (X.label R V) (X.label R B) hc hp hq hC hm ℓ hInd hq' hδ' D)
    change predicate _ _ _ _ _ _ = predicate K' q' (X.label R V) (X.label R B) (silent q' S D) _
    apply congr_arg (predicate K' q' (X.label R V) (X.label R B) (silent q' S D)); unfold power; simp only [Rotation.label]; ring
where
   filter_mono_lt {w r : ℝ}(hw:w<r-0):∀ᶠ δ in 𝓝 (0:ℝ), w<r-δ:=by
       filter_upwards [gt_mem_nhds (show 0<r-w from by linarith)] with δ h
       linarith only [h]

private lemma enclose (hε:0<ε) : predicate K q V B (ok q o S) (power V B o ε):=by
    classical
    let P:=ok q o S; let p:=power V B o ε
    have he:= pocket hO q V B o ε K hK hsafe hT hh hm hc hp hq hC hG hε
    choose U hU hg using he
    obtain ⟨t,ht⟩:= hK.elim_nhds_subcover' _ hU
    let W (x:t):=U x.val x.val.property
    have hpr(i:t):∃r:ℝ,0<r∧ ∀z∈K ∩ W i,∀c:ι→ℂ,(∑ i:ι,‖c i‖)≤1→P z c→∀y:E4,0<‖y‖→‖y‖ < r → ‖combo q V B c z y‖≤‖y‖^p:=by let x:=i.val; change ∃ r:ℝ,_; exact hg (x:K) x.property -- maybe casts
    choose b hb hbound using hpr
    obtain ⟨r,hr,hb'⟩:=(show ∀ᶠ v:ℝ in 𝓝[>] (0:ℝ),0<v ∧∀i,v<b i from (show ∀ᶠv:ℝ in 𝓝[>] (0:ℝ),0<v from self_mem_nhdsWithin).and ((eventually_all.mpr fun i=>gt_mem_nhds (hb i)).filter_mono nhdsWithin_le_nhds)).exists
    refine ⟨r,hr,fun z hz c hc Hp y hy hy' =>?_⟩
    obtain ⟨x,s,hm⟩:= Set.mem_iUnion₂.mp (ht hz)
    let i:t:=⟨x,s⟩
    exact hbound i z (Set.mem_inter hz hm) c hc Hp y hy (lt_trans hy' (hb' i))

/-! Anchor-first pair estimates on the same unselected Table. -/
lemma pairSigned (D:ℕ):predicate K q V B (silent q S D) (-(B.1:ℝ)-V.1+D+1/64):=Eq.mp (show predicate K q V B (ok q (some D) S) (power V B (some D) 1) = _ from congr_arg (predicate K q V B (silent q S D)) (by unfold power; ring)) (enclose hO q V B (some D) 1 K hK hsafe hT hh hm hc hp hq hC hG one_pos)
lemma pairOrdinary (hε:0<ε):predicate K q V B (fun _ _=>True) (-(B.1:ℝ)-V.1-ε):=Eq.mp (show predicate K q V B (ok q none S) (power V B none ε)=predicate K q V B (fun _ _=>True) ((-(B.1:ℝ))-V.1-ε) from congr_arg (predicate K q V B ((ok q none S))) (by unfold power; ring)) (enclose hO q V B none ε K hK hsafe hT hh hm hc hp hq hC hG hε)

end YM.MultipleContact.Local
