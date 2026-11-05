import YM.TraceExtension.Perfect.Mail

/-!
# Rooted germ gauge. Only need under analytic tests; allows torus derivatives directly. No translation assertion intermediate.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Perfect
open Function Filter Matrix Lattice Precision Laurent Stationary Bloch Exterior Tree RG Wilson
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius
variable {c f:Side}{S:StepData c f}{G:Gauge}{p u:Clip}{M R:PathData G}{η α C D ℇ:ℝ}
variable {T : Type}[NormedAddCommGroup T][NormedSpace ℝ T] [FiniteDimensional ℝ T] [CompleteSpace T]

def Dresses {G:Gauge}{n : Side}(f:Config G n → ℝ)(T:Type)[NormedAddCommGroup T][NormedSpace ℝ T]: Prop:=
    ∀ (V:T → Config G n)(k:T→Coats G n)(u:G.El), Army V 0 → V 0=1 → Army k 0 → k 0=(fun _=>u) → (fun x=> f (Lattice.gauge (k x) (V x)))=ᶠ[𝓝 0] f ∘ V

def Mails {G:Gauge}{n : Side}(f:Config G n → Link G n)(T:Type)[NormedAddCommGroup T][NormedSpace ℝ T]: Prop:=
    ∀ (V:T → Config G n)(k:T→Coats G n)(u:G.El), Army V 0 → V 0=1 → Army k 0 → k 0=(fun _=>u) → (fun x=> f (Lattice.gauge (k x) (V x)))=ᶠ[𝓝 0] (fun x=> armor (k x) (f (V x)))
structure Cleric {G:Gauge}{n:Side}(f:Config G n→ℝ) : Prop where
    dye : ContDiffAt ℝ ω (f ∘ input G n) 0
    jacket (T:Type) [NormedAddCommGroup T] [NormedSpace ℝ T] [FiniteDimensional ℝ T] [CompleteSpace T] : Dresses f T
structure Cloaked {G:Gauge}{n:Side}(f:Config G n→Link G n) : Prop where
    dye : ContDiffAt ℝ ω (f ∘ input G n) 0
    jacket (T:Type) [NormedAddCommGroup T] [NormedSpace ℝ T] [FiniteDimensional ℝ T] [CompleteSpace T] : Mails f T

variable {n : Side} {fₛ : Config G n→ ℝ}{fᵧ : Config G n→ Link G n}
private lemma liftA {Y: Type}[NormedAddCommGroup Y][NormedSpace ℝ Y](g: Config G n→Y)(U:T→Config G n)(h:ContDiffAt ℝ ω (g∘ input G n) 0)(hp:Army U 0)(he:U 0=1): ContDiffAt ℝ ω (g ∘ U) 0:=by
    let S x:= content (U x)
    apply ContDiffAt.congr_of_eventuallyEq (f:=(g ∘ input G n) ∘ S)
    · apply ContDiffAt.comp _ _ (hp.logL he); rw [he,content_one];exact h
    filter_upwards [(show Tendsto U _ (𝓝 1) from he ▸ hp.cont.tendsto).eventually content_encodes] with x hx; exact congr_arg g hx.symm
lemma Cleric.put (h:Cleric fₛ) (U:T→Config G n) (he:Army U 0)(hv:U 0=1): ContDiffAt ℝ ω (fₛ ∘ U) 0:= liftA _ _ h.dye he hv
lemma Cloaked.put (h:Cloaked fᵧ)(U:T→Config G n)(he:Army U 0)(hv:U 0=1): ContDiffAt ℝ ω (fᵧ ∘ U) 0:= liftA _ _ h.dye he hv

variable {F:Forest S.ratio}{r: Bid.Dir G c→AxisChart G F} (u: G.El)
private lemma boots_identity : boots S F (1:Joint G c f)=1:=by
 unfold boots trousers; rw [show ((1:Joint G c f).2 ∘ S.ratio.parent)=1 from rfl,wages_zero]
 funext i; have hz:= Push.stroll_zero (G:=G) (F.hike i) i
 rw [link_one] at hz
 simp [Function.comp_apply,Tree.Forest.foldAt,hz]
lemma strip_roots (u:G.El): Lattice.gauge (fun _:Site n=>u) (1:Config G n)=1:=by funext x;simp [Lattice.gauge]

variable (t:S.Choices)(h:Critical F p M r)(hy:S.patch.Branches S.kernel G)(hz:M.Bounds p η C D)(he:PriceGap F p M α)(hp:0 < α)
local notation "Cont_"=> encamp F r
-- transfer origin analyt and transport under any gauge family via veterans. parameterized by gauge group element; doesn't change tag.
include t h hy hz he hp
private lemma stretch {V:T→Config G c}{k:T→Coats G c}(u:G.El)(hV:Army V 0)(h1:V 0=1)(hk:Army k 0)(hw:k 0=(fun _=>u)):
     let U:=fun x=>encamp F r (content (V x)); let V':=fun x=>Lattice.gauge (k x) (V x); let W x:=wages S (fun _=>u) (k x) (U x)
     let C':=fun x=>boots S F (W x)*(fun _=>u)
     Army C' 0 ∧ C' 0=(fun _=>u) ∧ Thaw (fun x=> wages S (C' x) (k x) (U x)) 0 ∧ (fun x=>encamp F r (content (V' x)))=ᶠ[𝓝 0] (fun x=> wages S (C' x) (k x) (U x)):=by
    intro U V' W C'
    let F':= (fun _:Site f=>u)
    have hL : V' 0=1:= by unfold V'; rw [hw,h1]; exact strip_roots u
    have hc : Army V' 0:= hk.slant hV; let Y x :=content (V x); let Z x:=content (V' x)
    have hy': Y 0=0:=by unfold Y; rw [h1,content_one]
    have hZ : Z 0=0:=by unfold Z; rw [hL,content_one]
    have hx : Thaw U 0:= Thaw.comp (w:=Y) (g:=encamp F r) (x:=0) (hy'.symm ▸ camp_thaw h) (hV.logL h1)
    have hx' : Army (fun x=>boots S F (W x)) 0:= boot_lit S _ (hx.wages S (Army.park F' _) hk)
    have he' : U 0=1:=by change encamp F r (Y 0)=1; rw [hy',encamp_zero h]
    have ha : W 0=1:=by unfold W; rw [hw,he']; ext a <;> simp [wages,Lattice.gauge]
    have hU(Z:Joint G c f)(k:Coats G f) (s:Coats G c): cloak S F (wages S k s Z)=wages S (boots S F (wages S k s Z)*k) s Z:= by rw [cloak,wage_comp,one_mul]
    refine ⟨hx'.mul (Army.park F' _),?_,(hx.wages S (hx'.mul (Army.park F' _)) hk),?_⟩
    · unfold C'; rw [ha,boots_identity,one_mul]
    let A x:= cloak S F (W x)
    have hG : ∀ᶠ x in 𝓝 0, A x=encamp F r (Z x) :=by
       apply veterans h hy hz he hp t (hx.wages S (Army.park F' _) hk) ha (hc.logL hL) hZ
       filter_upwards [(show Tendsto Y _ (𝓝 0) from hy' ▸ (hV.logL h1).continuousAt.tendsto).eventually (camp_station h hy hz t),(show Tendsto V' _ (𝓝 1) from hL ▸ hc.cont.tendsto).eventually content_encodes,(show Tendsto V _ (𝓝 1) from h1 ▸ hV.cont.tendsto).eventually content_encodes] with x hx hu hv
       rw [show input G c (Z x)=_ from hu,show V' x=Lattice.gauge (k x) (input G c (Y x)) from congr_arg (Lattice.gauge _) hv.symm]; exact Shell.wage hy hz hx F' (k x)
    filter_upwards [hG] with x hx; exact hx.symm.trans (hU (U x) _ (k x))
variable (F r) in
def inheritJ (fₛ:Config G f→ℝ)(V:Config G c):ℝ:= fₛ (encamp F r (content V)).1
variable (F r) in
def inheritY (fᵧ:Config G f→Link G f)(V:Config G c):Link G c:=
   let U:=encamp F r (content V); shuttle S t U V (fᵧ U.1)

variable {J:Config G f→ℝ}{Y:Config G f→ Link G f}
omit t h hy hz he hp in
lemma inspire : (inheritJ F r J) ∘ input G c =ᶠ[𝓝 0] fun x=> J (Cont_ x).1:= by
 filter_upwards [input_encodes (G:=G) (m:=c)] with v hv; rw [Function.comp_apply,inheritJ,hv]
omit h hy hz he hp in
lemma inmate : (inheritY F r t Y) ∘ input G c =ᶠ[𝓝 0] fun x=> shuttle S t (Cont_ x) (input G c x) (Y (Cont_ x).1):=by
 filter_upwards [input_encodes (G:=G) (m:=c)] with v hv; simp only [Function.comp_apply,inheritY,hv]
lemma flashes (hJ:Cleric J) : Cleric (inheritJ F r J) :=by
    refine ⟨(hJ.put _ (camp_thaw h|>.1) (congr_arg Prod.fst (encamp_zero h))).congr_of_eventuallyEq inspire,?_⟩
    intro T _ _ _ _ V k u hV h1 hk hw
    let W:=fun x=> encamp F r (content (V x))
    obtain ⟨hg,hg',hc,hh⟩:= stretch t h hy hz he hp u hV h1 hk hw
    have hW : Thaw W 0:= (Thaw.comp (g:=encamp F r) (w:=content ∘ V) (x:=0) (by rw [Function.comp_apply,h1,content_one]; exact camp_thaw h) (hV.logL h1)); have hQ:W 0=1:=by unfold W; rw [h1,content_one,encamp_zero h]
    filter_upwards [hh,hJ.jacket T _ _ _ hW.1 (congr_arg Prod.fst hQ) hg hg'] with x hC hx
    exact (congr_arg (fun U=>J U.1) hC).trans hx
set_option maxRecDepth 8192 in
lemma flair (hY:Cloaked Y): Cloaked (inheritY F r t Y):=by
    let U:=Cont_
    have hU : Thaw U 0:=camp_thaw h
    have h' : U 0=1:= encamp_zero h
    refine ⟨(steering t hy (fun x=> Y (U x).1) (hY.put _ hU.1 (congr_arg Prod.fst h')) hU h' (Army.powL (v:=id) contDiffAt_id)).congr_of_eventuallyEq (inmate t),?_⟩
    intro T _ _ _ _ V k u hV h1 hk hw
    let W x:= U (content (V x))
    obtain ⟨hg,hg',hc,hh⟩:= stretch t h hy hz he hp u hV h1 hk hw
    let g x:= boots S F (wages S (fun _=>u) (k x) (W x))*(fun _=>u)
    have hW : Thaw W 0:= (Thaw.comp (g:=U) (w:=content ∘ V) (x:=0) (by rw [Function.comp_apply,h1,content_one]; exact hU) (hV.logL h1))
    have hW': W 0=1:=by unfold W;rw [h1,content_one,h']
    have ha : (wages S (g 0) (k 0) (W 0)).1=1:=by rw [show g 0 = _ from hg',hW']; exact strip_roots u
    filter_upwards [hh,hY.jacket T _ _ _ hW.1 (congr_arg Prod.fst hW') hg hg',Stationary.awake t hz hW (by rw [hW'];rfl) hy root_customs, Stationary.awake t hz hc ha hy root_customs] with x hQ hx hv he
    have hd := shuttle_turn t (V x) hy (g x) (k x) hv he (Y (W x).1)
    change shuttle S t (U _) _ (Y ((U (content (Lattice.gauge (k x) (V x)))).1))=_; rw [show U (content (Lattice.gauge (k x) (V x))) = _ from hQ]
    rw [← show Y (wages S (g x) (k x) (W x)).1 =armor (g x) (Y (W x).1) from hx] at hd
    change shuttle S t (wages S (g x) (k x) (W x)) _ _ = armor (k x) (shuttle S t (W x) (V x) (Y (W x).1))
    exact hd
end YM.Trace.Perfect
