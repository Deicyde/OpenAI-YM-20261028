import YM.TraceExtension.Filch.Herd
import YM.TraceExtension.Det.Kith
set_option autoImplicit false
/-! # lifted tangent and flow. -/
noncomputable section
namespace YM.Trace.Filch
open Function Filter Matrix Lattice Precision Laurent Stationary Perfect Exterior Tree RG Wilson Finset Push.Uniform Det
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{n:Side}
variable {X : Type}[NormedAddCommGroup X][NormedSpace ℝ X]

def patio(o:Site n)(k:ℕ)(U:Config G n)(v:Link G n):Acr G n:=
    (bite G n).symm (edgeColor.symm (fun i=> nimbus G k (flock o U i)), armor (march o U) v)
private abbrev U(G:Gauge)(n:Side):= input G n ∘ aleft G n
lemma patioA(o:Site n)(x:Link G n × Link G n)(i:Lines G n 1): (bite G n).symm x (Sum.inl i)=x.1 i:=rfl
lemma patioB(o:Site n)(x:Link G n × Link G n)(i:Lines G n 1): (bite G n).symm x (Sum.inr i)=x.2 i:=rfl
lemma patioX(o:Site n)(k:ℕ)(U:Config G n)(v:Link G n)(x:Site n)(b:Axis)(i:G.ColorIndex): patio o k U v (.inl (x,coord b,i))= nimbus G k (flock o U (x,b)) i:=by
    unfold patio; rw[patioA o]; change edgeColor (edgeColor.symm _) (x,b) i=_; simp
lemma patioY(o:Site n)(k:ℕ)(U:Config G n)(v:Link G n)(x:Site n)(b:Axis)(i:G.ColorIndex): patio o k U v (.inr (x,coord b,i))= G.adjoint (march o U x) (edgeColor v (x,b)) i:=by unfold patio; rw [patioB o]; change edgeColor (armor _ _) (x,b) i=_; rw[armor_at]
def par(o:Site n)(k:ℕ)(v:Acr G n):= patio o k (U G n v) (aright G n v)
def exactP(o:Site n)(v:Acr G n):= (bite G n).symm (content (flock o (U G n v)), armor (march o (U G n v)) (aright G n v))
def loyG (W:Coats G n): Acr G n→L[ℝ] Acr G n:= (bite G n).symm.toContinuousLinearMap ∘L (((armor W).prodMap (armor W)) ∘L (bite G n).toContinuousLinearMap)
lemma loyX(W:Coats G n)(v:Acr G n): bite G n (loyG W v)=(armor W (aleft G n v),armor W (aright G n v)):=by unfold loyG; simp;rfl
lemma loyY(o:Site n)(k:ℕ)(Z:Config G n)(W:Coats G n)(v:Link G n): patio o k (Lattice.gauge W Z) (armor W v)= loyG (fun _=>W o) (patio o k Z v):=by
    apply (bite G n).injective; rw[loyX]; unfold patio; simp
    refine And.intro (edgeColor.injective (funext fun i=>?_)) (edgeColor.injective (funext (fun e : Edge (Site n)=>?_)))
    · simp only [armor_at,ContinuousLinearEquiv.apply_symm_apply]; rw [heaved,altoM]
    change edgeColor (armor _ _) _ = edgeColor (armor _ _) _; rw [armor_at,armor_at,armor_at,armor_at,← G.adjoint_mul,← G.adjoint_mul,herald]; group
private lemma adInner (u:G.El)(x y:G.Color): inner ℝ (G.adjoint u x) (G.adjoint u y)= inner ℝ x y:= (show G.Color→ₗᵢ[ℝ] G.Color from ⟨G.adjoint u,G.norm_adjoint u⟩).inner_map_map _ _
lemma loyS (W:Coats G n)(x y:Link G n): (armor W x) ⬝ᵥ (armor W y)=x ⬝ᵥ y:=by simp_rw [dotEdge,armor_at,adInner]
private lemma glows {U:X→ Config G n}(o:Site n){v:X→ Link G n}{x:X}(he:Army U x)(ht: ContDiffAt ℝ ω v x): ContDiffAt ℝ ω (fun y=> armor (march o (U y)) (v y)) x:=by
    let K:=fun y=> armor (march o (U y)) (v y)
    let A e:=fun y=> (G.adjoint (march o (U y) e)).toContinuousLinearMap
    obtain ⟨C,_,H⟩:= Planned.PrimaryIntegral295.Drupes.shaders G 0
    have hQ : ContDiffAt ℝ ω (edgeColor ∘ K) x:=by
       apply contDiffAt_pi.mpr; intro j; let k y:= G.mat (march o (U y) j.1)
       have ha:ContDiffAt ℝ ω (A j.1) x:=by unfold A; simp_rw[Planned.PrimaryIntegral295.Drupes.turned]; exact ((H _).analytic.comp (f:=k) _ (herd_warm o U x he j.1))
       have hb:ContDiffAt ℝ ω (fun y=> edgeColor (v y) j) x:=contDiffAt_pi.mp (edgeColor.contDiff.contDiffAt.comp _ ht) j
       exact (ha.clm_apply hb).congr_of_eventuallyEq (Eventually.of_forall fun y=> armor_at ..)
    refine (edgeColor.symm.contDiff.contDiffAt.comp _ hQ).congr_of_eventuallyEq (Eventually.of_forall fun y=>?_); exact (edgeColor.symm_apply_apply (K y)).symm
lemma patioW(o:Site n)(k:ℕ)(U:X→ Config G n)(v:X→ Link G n)(x:X)(h:Army U x)(he:ContDiffAt ℝ ω v x): ContDiffAt ℝ ω (fun y=> patio o k (U y) (v y)) x:=
    (bite G n).symm.contDiff.contDiffAt.comp _ ((edgeColor.symm.contDiff.contDiffAt.comp _ (f:=fun y=> fun i=>nimbus G k (flock o (U y) i)) (contDiffAt_pi.mpr (fun i=> radiant (fun y=>flock o (U y) i) x (flock_warm o U x h i) k))).prodMk (glows o h he))
private lemma UV (x:Acr G n): Army (U G n) x:=Army.powL (aleft G n).contDiff.contDiffAt
private lemma U0 (G:Gauge)(n): U G n 0=1:=by unfold U; simp
lemma parW(o:Site n)(k:ℕ) (x:Acr G n): ContDiffAt ℝ ω (par (G:=G) o k) x:= patioW o k (U G n) (aright G n) x (UV _) (aright G n).contDiff.contDiffAt
lemma exactW(o:Site n): ContDiffAt ℝ ω (exactP (G:=G) o) 0:=
   (bite G n).symm.contDiff.contDiffAt.comp _ ((show ContDiffAt ℝ ω (fun y=> content ((flock o ∘ U G n) y)) 0 from (flock_warm o _ _ (UV _)).logL (by rw[Function.comp_apply,U0,flock_zero])).prodMk (glows o (UV _) (aright G n).contDiff.contDiffAt))
lemma parZ(o:Site n)(k:ℕ): par (G:=G) o k 0=0:=by
    unfold par patio; rw[map_zero (aright ..),U0,flock_zero];simp[rain_zero];rfl
lemma exactZ(o:Site n):exactP (G:=G) o 0=0:=by
    unfold exactP; rw[U0,flock_zero];simp
private lemma braid_a {F H:X→ Acr G n}(hF:ContDiffAt ℝ ω F 0)(hH:ContDiffAt ℝ ω H 0){k:ℕ}(hx:∀ j,braid (fun a=> F a j) (fun a=>H a j) 0 k): braid F H 0 k:=by
    intro i hi; ext1 v; ext1 j
    let L:= ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _:pairA G n=>ℝ) j
    have he:= DFunLike.congr_fun (show iteratedFDeriv ℝ i (L ∘ F) 0=_ from hx j i hi) v; rw [L.iteratedFDeriv_comp_left hF le_top,show (fun a=>H a j)=L ∘ H from rfl,L.iteratedFDeriv_comp_left hH le_top] at he; exact he
lemma par_charm(o:Site n)(k:ℕ): braid (exactP (G:=G) o) (par o k) 0 k:=by
   refine braid_a (exactW _) (parW ..) (fun j=>?_); cases j with
   | inr j=> intro i _; rfl
   | inl j=>
     rcases j with ⟨y,b,l⟩; obtain ⟨b,rfl⟩:= axisEquiv.surjective b
     let F(z:Acr G n):= flock o (U G n z) (y,b); have hf: F 0=1:=by simp[F,flock_zero]
     have hx:ContDiffAt ℝ ω (G.mat ∘ F) 0:=flock_warm o _ _ (UV _) (y,b)
     let L:G.Color→L[ℝ] ℝ:=EuclideanSpace.proj l; have hz:ContDiffAt ℝ ω (G.plog ∘ G.mat ∘ F) 0:= ContDiffAt.comp 0 (g:=G.plog) (by simp only [Function.comp_apply,hf,G.mat_one]; exact G.plog_diff) hx
     intro i hi
     rw [show (fun a:Acr G n=> exactP o a (.inl (y,axisEquiv b,l)))= L ∘ G.plog ∘ G.mat ∘ F from funext (fun a=> congr_arg (fun x:G.Color=> x l) (content_at (flock o _) y b)), show (fun a:Acr G n=> par o k a (.inl (y,axisEquiv b,l)))= L ∘ nimbus G k ∘ F from funext (fun a=> patioX o k ..), L.iteratedFDeriv_comp_left hz le_top, L.iteratedFDeriv_comp_left (radiant F 0 hx _) le_top,resounds F hf hx k i hi]
private lemma Uturned(u:G.El)(v:Acr G n): U G n (loyG (fun _=>u) v)=Lattice.gauge (fun _=>u) (U G n v):=by
   let W:Coats G n:=fun _=>u
   have hh:=armor_go W (aleft G n v) 1; rw [strip_roots u,mul_one,mul_one] at hh; (exact (congr_arg (input G n) (congr_arg Prod.fst (loyX W v))).trans hh)
lemma glowB{F:Peat G n}(h: Cleric F) (u:G.El): ballX F =ᶠ[𝓝 0] ballX F ∘ loyG (fun _=>u):=by
    filter_upwards [h.jacket (Acr G n) (U G n) (fun _ _=>u) u (UV _) (U0 _ _) (Army.park _ _) rfl] with v hv
    exact hv.symm.trans (congr_arg F (Uturned u v).symm)
lemma glowP{F:Peat G n}(h:Cleric F)(o:Site n): ballX F=ᶠ[𝓝 0] ballX F ∘ exactP o:=by
    let V:=flock o ∘ U G n
    have he:V 0=1:=by simp[V,flock_zero]
    have hv:Tendsto V _ (𝓝 1):= he ▸ (show Tendsto V (𝓝 0) (𝓝 (V 0)) from (flock_warm o _ _ (UV _)).cont.tendsto)
    filter_upwards [h.jacket (Acr G n) (U G n) (march o ∘ U G n) 1 (UV _) (U0 _ _) (herd_warm o _ _ (UV _)) (by rw[Function.comp_apply,U0,herd_zero];rfl), hv.eventually content_encodes] with z hz hh
    change F _=ballX F (exactP o z); unfold ballX exactP; rw[ContinuousLinearEquiv.apply_symm_apply, show input G n (content (flock o _))=_ from hh]; exact hz.symm
lemma bloomY{Y:Gal G n}(h:Cloaked Y)(u:G.El): bottom Y =ᶠ[𝓝 0] bottom Y ∘ loyG (fun _=>u):=by
   let W:Coats G n:=fun _=>u
   filter_upwards [h.jacket (Acr G n) (U G n) (fun _ _=>u) u (UV _) (U0 _ _) (Army.park _ _) rfl] with v hv
   change Y (U G n v) ⬝ᵥ aright G n v= Y (U G n (loyG W v)) ⬝ᵥ (bite G n (loyG W v)).2; rw[Uturned,loyX,show Y _=_ from hv]; exact (loyS W _ _).symm
lemma bloomP{Y:Gal G n}(h:Cloaked Y)(o:Site n): bottom Y=ᶠ[𝓝 0] bottom Y ∘ exactP o:=by
    let V:=flock o ∘ U G n
    have he:V 0=1:=by simp[V,flock_zero]
    have hv:Tendsto V _ (𝓝 1):=he ▸ (show Tendsto V (𝓝 0) (𝓝 (V 0)) from (flock_warm o _ _ (UV _)).cont.tendsto)
    filter_upwards [h.jacket (Acr G n) (U G n) (march o ∘ U G n) 1 (UV _) (U0 _ _) (herd_warm o _ _ (UV _)) (by rw[Function.comp_apply,U0,herd_zero];rfl), hv.eventually content_encodes] with z hz hh
    unfold bottom; simp only [Function.comp_apply, exactP, ContinuousLinearEquiv.apply_symm_apply]; change _= Y (input G n (content (V z))) ⬝ᵥ (armor (march o (U G n z)) (aright G n z)); rw[hh,show Y (V z) = _ from hz]; exact (loyS _ _ _).symm
end YM.Trace.Filch
