import YM.TraceExtension.Loft.Waters
set_option autoImplicit false
/-!
# VIZ with Wilson specialization. No mollifier short distance assertion here;
formal coefficient test is local quadratic of exact Haar Jacobian rooted current.
Resource for physical control at that scale.
-/
noncomputable section
namespace YM.Trace.Loft
open Function Filter Matrix Lattice Precision Laurent Stationary Perfect Bloch Exterior Tree RG RG.Supply Wilson Finset Push.Uniform Audience Metric Lamp Det Planned.PrimaryIntegral295 Next.Free Org Input Extra.Histories
open scoped BigOperators Topology ContDiff ComplexConjugate Classical
variable {W:Type}{g:W→Side}{F:Filter W}{G:Gauge}{f:Side}{M: Metals G}{D:Rolls M.p}{A:Alloy M D}{α σ a C:ℝ}
def crest (q:G.ColorIndex)(X:Axis→ Maze G f): ℂ:= suite fun d i=> ∑ b,pia d i q b (X b)
def Helm (Q: Dart G f)(q:G.ColorIndex):ℝ:= (crest q (fun b:Axis=> lush (Q.Y b 0) ∘ input G f)).re
lemma crest_v {ε':W→ℝ}{p:Clip}{K:W→PathData G}{Z:∀ w,Dart G (g w)}(q:G.ColorIndex)(h:Scene g Z p K a C ε')(hp:Tendsto (fun w=>(g w).val) F atTop): Rose F (fun w=> Helm (Z w) q) (fun w=> (xup q (fun b:Axis=> lush ((Z w).Y b 0) ∘ input G (g w))).re):=by
   let Y(w)(b):=(Z w).Y b (0:Site (g w)); let X(w)(b): Maze G (g w):= lush (Y w b) ∘ input G (g w)
   refine Rose.side (CohX (f:=fun w=>xup q (X w)) (g:=fun w=> crest q (X w)) Complex.reCLM ?_)
   refine suite_hold (F:=fun w d i=> fata d i q (X w)) (fun d i=> Rose.sumX (s:=univ) (fun b _=> lux_neap d i q hp (fun w=> X w b) ?_ b))
   have hz(w):Y w b∈rains G _:= (h.house w|>.sound.palm b 0)
   have hk:=h.c0; have ha:=h.vp
   obtain ⟨T,hT,H⟩:=pipe_w G 3
   let c:= a/5/4/5;have hc:0 < c:=by unfold c; positivity
   have hx:0 ≤ T*C*(Fintype.card (Loc G 1))*countCost c:=by have h:= count_pos hc; positivity
   refine ⟨c,_,hc,hx,fun w=>?_⟩
   have he : Cloaked (Y w b) := (hz w).1
   have hu := H (g w) (Y w b) (0:Site (g w)) C (a/5) (by positivity) hk he (pea_rain (hz w) ((h.house w).Y b _) hk ha.le)
   have hp: PetW (0:Site (g w)) (tidal (Y w b) ∘ input G (g w)) c (T*C) 2:= by
       apply tidal_pay _ he; intro i; have hf:= hu i; rwa[show a/5/((↑(3:ℕ):ℝ)+1)/((↑(3:ℕ):ℝ)+2)=c by unfold c; norm_num] at hf
   exact pet_lush _ hp hc (by positivity)
lemma upsize {Z:Dart G f}{ε δ:ℝ}{d e v u:ℕ→ℝ}{R:PathData G}{p:Clip}(h:Viz Z p R a d e ε)(hp: ε ≤ δ)(he:∀ i,i≤4→ 2 ≤ i → d i ≤ v i) (hv:∀ i,i≤4→ 2 ≤ i→ e i ≤ u i): Viz Z p R a v u δ:=by
    have hx(_d _v:ℕ→ℝ){x:Site f}{J:Acr G f → ℝ} (H: Estate x J a _d)(hp:∀ i,i≤4→ 2 ≤ i→ _d i ≤ _v i): Estate x J a _v := ⟨fun i hi hk=> (H.values i hi hk).trans (hp i hi hk)⟩
    exact ⟨h.sound,fun i j t=>hx d _ (h.J i j t) he,fun i t=>hx _ _ (h.Y i t) he,fun i t=>hx _ _ (h.E i t) hv,fun i t=>hx _ _ (h.plum i t) he,fun i j k t=>hx _ _ (h.mint i j k t) he,fun i j x=>⟨fun s t hv=> ((h.ox i j x).bill s t hv).trans hp⟩, fun i x=>⟨fun s t hv=> ((h.orb i x).bill s t hv).trans hp⟩⟩
lemma vizwire (A:Alloy M D)(k:ℕ)(hG:G.Simple)(δ:ℝ)(hd:0 < δ)(ha:0 < a)(hc:0 ≤ C):∃ x:ℝ,0< x ∧ ∃ T:ℕ,∀ (N p:ℕ), k<N→ T≤ p→ let f:=A.B.a.S.side k p; let s:= A.B.a.params k; ∀ Q:Dart G f,Q.March → (Viz Q s.clip (A.B.kin.path N k) a (fun _=>C) (fun _=>x) x)→∀ q, |Helm Q q - landPay G| ≤ δ:=by
    classical
    by_contra! he
    let u(i:ℕ):ℝ:=1/(1+i)
    have hu(i):0<u i:=by unfold u; positivity
    have hx:Tendsto u atTop (𝓝 0):= tendsto_const_nhds.div_atTop (tendsto_atTop_mono (f:=fun x:ℕ=>(x:ℝ)) (fun x=> le_add_of_nonneg_left (by norm_num : 0≤(1:ℝ))) tendsto_natCast_atTop_atTop)
    -- see normalized nnf
    simp only[not_forall,exists_prop,not_le] at he
    choose N p hn hp Q hQ hV b hy using fun i=> he (u i) (hu i) i
    let s:=A.B.a.params k; let g(i:ℕ):=A.B.a.S.side k (p i); let R(i):=A.B.kin.path (N i) k
    have hf:Tendsto (fun w=>(g w).val) atTop atTop:= (deep_n A.B.a.S k).comp (tendsto_atTop_mono hp tendsto_id)
    obtain ⟨H,Y,X,E,ε,σ,U,W,h⟩:=colorWire N p k hn hG A
    have ht:Scene g Q s.clip R a C u:= ⟨hV,hQ,ha,hc,fun i=> ⟨(hu i).le,div_le_self zero_le_one (le_add_of_nonneg_right (by positivity))⟩⟩
    have hv (q:G.ColorIndex):= Rose.alight (crest_v q ht hf) (awake q h ht hf hx H hG s.width_pos)
    obtain ⟨i,hi⟩:= (eventually_all.mpr fun q=> (hv q).eventually (ball_mem_nhds _ hd)).exists
    exact not_lt_of_ge (le_of_lt (show |Helm (Q i) (b i)-landPay G|< δ by simpa [Real.dist_eq] using mem_ball.mp (hi (b i)))) (hy i)
def trophy (u:ℝ):= ∑ i∈range 5,|reed u i+1|
include A
lemma news (B:Bolt A)(V:Vigil A.B.a) (hG:G.Simple): ∀ᶠ k:ℕ in atTop,∀ ε:ℝ,0< ε → ∀ (F:Filter W)(N p:W→ℕ), Tendsto N F atTop → Tendsto p F atTop → ∀ᶠ w in F,
    let Z:=(Issue.trail B).rep (N w) (p w) k; let x:=A.B.a.clock.hatBeta k
    ∃ Q:Dart G (A.B.a.S.side k (p w)), Viz Q Z.clip Z.path (east x) (fun _=> trophy x) (fun _=> ε) ε ∧ Q.March ∧ ∀ q:G.ColorIndex, |Helm Q q- landPay G| ≤ ε:=by
    filter_upwards[treasury (W:=W) V B] with k hk ε hε F N p hN hp
    let φ:=A.B.a.clock.hatBeta k; have hh:0≤ trophy φ:=sum_nonneg fun i _=>abs_nonneg _; have he:0<east φ:=inv_pos.mpr (Real.log_pos (A.B.a.fits.delayed k))
    obtain ⟨x,hx,T,H⟩:= vizwire A k hG ε hε he hh
    let y:=min ε x; have hz:0 < y:=lt_min hε hx
    filter_upwards [hk y hz F N p hN (fun i=> (deep_n A.B.a.S i).comp hp),hp.eventually_ge_atTop T,hN.eventually (eventually_gt_atTop k)] with w hw hv hw'
    intro R Y; let K:= A.B.kin.path (N w) k; let s:= A.B.a.params k
    have h1:R.clip=s.clip:= (B.choice.represents (N w) (p w) k hw'.le).clip; have h2:R.path=K:=(actual_path B (N w) k (p w) hw'.le).symm
    obtain ⟨Q,hQ⟩:=hw; change Viz Q R.clip R.path (east φ) _ _ _ at hQ;rw[h1,h2] at hQ ⊢
    have hx (i:ℕ)(hi:i ≤ 4):reed φ i+1≤ trophy φ:= (le_abs_self _).trans (single_le_sum (f:=fun i=>|reed φ i+1|) (fun i _=>abs_nonneg _) (mem_range.mpr (by omega)))
    have hh:=Q.gull (A.B.support.cap (N w) k hw'.le) hQ
    exact ⟨Q.sing,upsize hh (min_le_left ..) (fun i hi _=>hx i hi) (fun _ _ _=> min_le_left ..), Q.singed,H (N w) (p w) hw' hv Q.sing Q.singed (upsize hh (min_le_right ..) (fun i hi _=> hx i hi) (fun _ _ _=>min_le_right ..))⟩
end YM.Trace.Loft
#print axioms YM.Trace.Loft.news
