import YM.MultipleContact.Bunch.Scale
import YM.MultipleContact.Matching.Pocket

/-! Removing seam restrictions by fixed rotations on entire exterior collections
on finite compact subcovers, jointly for all slots (comparable scales). -/
set_option autoImplicit false
noncomputable section
namespace YM.MultipleContact.Bunching
open Filter Function MeasureTheory Analysis Extraction Table Ward MergeProof Acme Ribbons Around Cells Wilson Lattice Climb Set Metric
open Matching Local
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {G:Gauge}{C:Family G}{S:Table C.book}{F:Extraction.Order}{W:DiffPlan S} {D n':ℕ} [Inhabited (Fin n')]
variable {ι:Type*}[Fintype ι]{n:ι→ℕ}
variable {X:S.Rotation}
private def lit (R:Ortho)(q:C.book.Token):C.book.Token:=expose (X.label R (S.classTokens q))
private lemma lit_apply {X:S.Rotation} (R:Ortho)(q:C.book.Token):S.classTokens (lit (X:=X) R q)=X.label R (S.classTokens q):=by
      dsimp only [lit,expose,Rotation.label,classTokens]; congr 1;exact (S.rep ..)
omit [Fintype ι] [Inhabited (Fin n')] in
private lemma continuous_move_val (R:Ortho)(u:ι):Continuous (fun z:Points (n u) => Points.move R z):=by
    unfold Points.move points
    exact (PiLp.continuous_toLp _ _).comp (continuous_pi fun i=> (Ortho.motion R).continuous.comp (show Continuous (fun x:Points _=>x i) from by fun_prop))
private def repack (R:Ortho)(z:∀i,Points (n i)):=fun i=>Points.move R (z i)
private lemma continuous_repack (R:Ortho) : Continuous (repack (n:=n) R):=continuous_pi fun i=> (continuous_move_val R i).comp (continuous_apply i)
omit [Fintype ι] [Inhabited (Fin n')] in
lemma carries {n':ℕ}(R:Ortho)(y:E4)(z:Points n'):Points.move R (Points.cons y z)=Points.cons (Ortho.move R y) (Points.move R z):=by ext1 i; exact Fin.cases rfl (fun j=>rfl) i

variable (ρ:S.RealSpin)(hx:X.Laws W ρ)(hO:X.Oriented S)
include hO
omit [Fintype ι] [Inhabited (Fin n')] in
lemma rot_once {n':ℕ}(R:Ortho)(v:S.Tag)(q:Fin n'→ C.book.Token)(z:Points n')(he:Points.cons 0 z∈conf _): once q v z=once (lit (X:=X) R∘q) (X.label R v) (Points.move R z):=by
      have hx:= hO _ (Fin.cons (α:=fun _=>S.Tag) v (S.classTokens∘q)) (Points.cons 0 z) he R
      rw [carries,show R.move 0=0 from (R.motion).map_zero,Work.A01.comp_cons] at hx
      unfold once disc; rw [hx.symm]
      congr 2
      ext1 j
      exact (lit_apply ..).symm

omit [Fintype ι] [Inhabited (Fin n')] in
lemma rot_many {m:ℕ}(R:Ortho)(V:Fin n'→S.Tag)(q:Fin m→ C.book.Token)(y:Fin n'→E4)(z:Points m)(he:lands y z∈conf _): many V q y z=many (X.label R ∘V) (lit (X:=X) R ∘q) (R.move∘ y) (Points.move R z):=by
      have h_eq:Points.move R (lands y z) =lands (R.move∘y) (Points.move R z):=by ext1 i;refine Fin.addCases (fun s=>?_ ) (fun s=>?_) i <;> simp [Points.move,points_apply,lands]
      have hV:= hO _ (Fin.append V (S.classTokens∘q)) _ he R
      rw [h_eq] at hV; unfold many disc; rw [hV.symm]; congr 1
      funext i; refine Fin.addCases (fun i=>?_) (fun j=>?_) i
      · rw [Function.comp_apply, Fin.append_left,Fin.append_left]; rfl
      rw [Function.comp_apply, Fin.append_right,Fin.append_right]; exact (lit_apply ..).symm

omit hO
variable (q:∀i:ι,Fin (n i)→ C.book.Token)(V:Fin n'→S.Tag)(lamp:Lattice.Side)(o:Option ℕ)(ε:ℝ)
private def holds (S:Table C.book) (z:∀i,Points (n i)) (c:ι→ℂ):Prop:=match o with | none=> True | some n=> silent q S n z c
private def power :ℝ:= -((massOf V):ℝ)+ (match o with | none=>(-ε) | some k=>(k+1/64))
variable (K:Set ((i:ι)→Points (n i)))(hK:IsCompact K)(hsafe:∀x∈K,∀i, Points.cons 0 (x i) ∈ conf (n i+1))
include hK hsafe hO
private lemma carry (R:Ortho)
   (he:Puff ((repack R)''K) (fun i=>lit (X:=X) R ∘ q i) ((X.label R) ∘V) lamp (holds (fun i=>lit (X:=X) R∘q i) o S) (power ((X.label R)∘V) o ε)):
     Puff K q V lamp (holds q o S) (power V o ε):=by
     let K':=repack R '' K
     obtain ⟨r,hr,hyo⟩:=he; obtain ⟨δ,hδ,hgap⟩:= gapK K hK hsafe
     refine ⟨min (δ/(4*lamp.val)) r,lt_min (by positivity) hr,fun z hz c hm hy r' hr' hq y hNear=>?_⟩
     have hc (i):lands y (z i)∈conf _:=by
          have he(s u) : y s ≠ z i u:=by
               have hz': δ < ‖z i u‖:=by have h:= hgap z hz i u.succ 0 u.succ_ne_zero; simpa [Points.cons] using h
               have hy:=hNear.2.2 s
               have hr' := (lt_div_iff₀ (by positivity : 0<(4*lamp.val:ℝ))).mp (hq.trans_le (min_le_left ..))
               intro hx; rw [hx] at hy; linarith only [hδ,hy,hr',hz']
          intro s u; revert u; refine Fin.addCases ?_ ?_ s
          · intro s u; refine Fin.addCases (fun u h=>?_) (fun v h=>?_) u
            · suffices s=u from congr_arg (Fin.castAdd _) this; by_contra hn; have h0 : y s=y u:=by simpa [lands] using h
              have ht:=hNear.2.1 s u hn; rw [h0,sub_self,norm_zero] at ht; linarith
            exact (he s v (by simpa [lands] using h)).elim
          intro s u; refine Fin.addCases (fun v h=>(he v s (by simpa [lands] using h.symm)).elim) (fun u h=>?_) u
          exact congr_arg (Fin.natAdd n') (Fin.succ_inj.mp (hsafe z hz i (show Points.cons 0 (z i) s.succ=Points.cons 0 (z i) u.succ from (by simpa [Points.cons,lands] using h))))
     have hZ : holds (fun i=>lit (X:=X) R∘q i) o S (repack R z) c:= by
          cases o with
          | none=>trivial
          | some D => intro v
                      have hv: v = X.act D R ((X.act D R).symm v) := ((X.act D R).apply_symm_apply _).symm
                      have hs:=hy ((X.act D R).symm v)
                      rw [hv];exact Eq.trans (Finset.sum_congr rfl fun i _=> congr_arg (c i * ·) (Eq.symm (rot_once hO R ⟨D,_⟩ (q i) (z i) (hsafe z hz i)))) hs
     have huN:Cord.Near n' lamp r' (R.move∘y):=by
           refine ⟨by unfold Function.comp; rw [hNear.1];exact R.motion.map_zero,
                   fun s s' h=> ?_, fun s=>by dsimp only [Function.comp_apply]; rw [R.move_norm]; exact hNear.2.2 s⟩
           dsimp only [Function.comp_apply]; rw [show R.move (y s)-R.move (y s')=R.move (y s-y s') from (R.motion.map_sub ..).symm, R.move_norm]; exact hNear.2.1 s s' h
     have h := hyo (repack R z) ⟨z,hz,rfl⟩ c hm hZ r' hr' ((lt_of_le_of_lt le_rfl hq).trans_le (min_le_right ..)) (R.move ∘y) huN
     change _ ≤ r'^power V o ε at h
     exact (congr_arg (‖·‖) (Finset.sum_congr rfl fun i (_:i∈(Finset.univ:Finset ι))=>congr_arg (c i * ·) (rot_many hO R V (q i) y (z i) (hc i)))).le.trans h
variable (hm:W.Derivatives S)(hc:S.Hierarchy)(hp:F.PointLimits C S)(hq:Cells.CellHyp C F)(hmk:C.Makes)(hT:Acme.Aroma C)(hh:Treasury C)(hG:G.Simple)
include hm hc hp hq hmk hT hh hG
private lemma room (hε:0<ε)(z:((i:ι)→Points (n i))) (hz:z∈K):∃ U∈𝓝 z,Puff (K∩U) q V lamp (holds q o S) (power V o ε):=by
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
    apply carry hO q V lamp o ε A hL (fun z hz i=>hsafe _ hz.1 i) R
    rcases o with _|D
    · have ht:= ordinary K' hL' hh' q' (X.label R ∘ V) lamp hc hp hq hmk hm hT hh ℓ hInd hq' hδ' hG ε hε
      convert ht using 1 <;> first|rfl|unfold power; simp only; ring
    refine Eq.mp ?_ (erased K' hL' hh' q' (X.label R ∘ V) lamp hc hp hq hmk hm hT hh ℓ hInd hq' hδ' hG D)
    change Puff _ q' _ _ (silent q' S D) _ = Puff _ q' _ _ (silent q' S D) _
    apply congr_arg (Puff K' q' (X.label R∘V) lamp (silent q' S D)); unfold power; ring
where
   filter_mono_lt {w r : ℝ}(hw:w<r-0):∀ᶠ δ in 𝓝 (0:ℝ), w<r-δ:=by
       filter_upwards [gt_mem_nhds (show 0<r-w from by linarith)] with δ h
       linarith only [h]

private lemma enclosed (hε:0<ε) : Puff K q V lamp (holds q o S) (power V o ε):=by
    classical
    let Cond:= holds q o S; let p:=power V o ε
    have he:= room hO q V lamp o ε K hK hsafe hm hc hp hq hmk hT hh hG hε
    choose U hU hg using he
    obtain ⟨t,ht⟩:= hK.elim_nhds_subcover' _ hU
    let W (x:t):=U x.val x.val.property
    have hpr(i:t):∃r₀> (0:ℝ), ∀z∈K ∩ W i,∀c:ι→ℂ,(∑i:ι,‖c i‖)≤1→ Cond z c→ ∀r:ℝ,0<r → r < r₀→ ∀ y:Fin n'→E4,Cord.Near n' lamp r y→ ‖blend q V c z y‖ ≤ r^p:=by let x:=i.val; change ∃ r:ℝ,_; exact hg (x:K) x.property
    choose b hb hbound using hpr
    obtain ⟨r,hr,hb'⟩:=(show ∀ᶠ v:ℝ in 𝓝[>] (0:ℝ),0<v ∧∀i,v<b i from (show ∀ᶠv:ℝ in 𝓝[>] (0:ℝ),0<v from self_mem_nhdsWithin).and ((eventually_all.mpr fun i=>gt_mem_nhds (hb i)).filter_mono nhdsWithin_le_nhds)).exists
    refine ⟨r,hr,fun z hz c hc Hp r' hr' hr'' y hy=>?_⟩
    obtain ⟨x,s,hm⟩:= Set.mem_iUnion₂.mp (ht hz)
    let i:t:=⟨x,s⟩
    exact hbound i z (Set.mem_inter hz hm) c hc Hp r' hr' (hr''.trans (hb' i)) y hy

theorem manySigned (D:ℕ):Puff K q V lamp (silent q S D) (-(massOf V:ℝ)+D+1/64) := by
      convert enclosed hO q V lamp (some D) 1 K hK hsafe hm hc hp hq hmk hT hh hG zero_lt_one using 1 <;> first|rfl|unfold power;ring
theorem manyOrdinary (ε:ℝ)(hε:0<ε):Puff K q V lamp (fun _ _=>True) (-(massOf V:ℝ)-ε) := by
      exact enclosed hO q V lamp none ε K hK hsafe hm hc hp hq hmk hT hh hG hε
end YM.MultipleContact.Bunching
