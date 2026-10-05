# BITOXIN 2
## 상태의 의존 관계와 오류 관측을 설계하는 QA

기술 백서 · 2026년 10월 5일 · 구현 버전 2.0

**검사 중인 계산이 중단되었다가 다시 이어져도, 그 상태는 보존되어야 한다.**

BITOXIN에서 차용할 개념은 실제 상태를 다음 연산으로 이어 주고, 중간 손상이 관측 가능한 실패로 드러나도록 검사하는 것이다. 독립된 기대값을 유지하면서 연산·스케줄링·수명 전이를 통과시킨다. 원래의 sleep/wakeup 병행 검사는 이 개념을 시스템 상태 보존에 적용한 사례다.

이 백서는 개념과 참조 구현을 구분한다. 2~7절과 11절은 GPR·메모리 검사 구현과 검증 증거를 다룬다. 8~10절은 같은 사고방식을 제품 자체의 QA에 적용하는 설계다. Compuon·HESM에 Linux 모듈을 배치하자는 제안이 아니며, LFSR나 어셈블리도 개념 차용의 필수 요소가 아니다.

> 핵심 주장: 특정 QA 시나리오 아래에서 발생한 상태 손상을 더 관측하기 쉽게 만들 수 있다. 임의의 미발견 결함을 일정한 확률이나 시간 안에 찾아낸다는 보장은 주장하지 않는다.

### 증거를 읽는 방법

| 구분 | 이 문서의 의미 |
|---|---|
| 구현·검증 | 현재 소스와 로컬 시험으로 확인한 동작 |
| 역사적 경험 | 작성자가 설명한 과거 현장 사례; 원시 측정 로그는 미제공 |
| 적용 제안 | Compuon·HESM에서 앞으로 실행할 QA 설계 |
| 미검증 | 실제 보드의 PM·DDR·BSP 동작과 제품별 개선 효과 |

원안: 첨부된 3쪽 문서와 BITOXIN 저장소의 2018년 계열 구현. 이 백서는 원안에 대한 공식 수상·인증·벤더 검증을 뜻하지 않는다. [1]

---page---

# 1. 문제와 실무적 가설

SoC의 안정성 결함은 한 부품의 단독 기능 검사에서는 드러나지 않을 수 있다. 작성자가 겪은 문제는 power sequence와 연관된 bit flip, register·cache·DRAM 사이의 상태 손상, 그리고 paging과 PM 동작이 결합되는 조건이었다. 이때 소프트웨어가 보드의 실제 전원·클록 시퀀스를 임의로 제어할 수 있는 범위에는 한계가 있다.

원래 사용 방식은 커널 모듈을 적재한 뒤 독립된 커널 스레드를 기존 QA 시나리오와 병행하는 것이었다. 외부 시나리오가 sleep/wakeup과 시스템 활동을 만들고, BITOXIN은 그 조건 아래에서 정상 결과가 알려진 계산을 계속 수행했다. 특정 vendor BSP의 paging/PM 결합 문제를 거의 100% 재현 가능하게 만들었다는 작성자의 회고가 있다. BSP 식별자, 보드 수, 반복 횟수, 대조군 및 원시 로그는 현재 자료에 없으므로, 이를 이번 구현의 측정 재현율로 표기하지 않는다. [1]

### 서로 다른 세 역할

[[mechanism]]

이 구성에서는 두 효과가 동시에 나타날 수 있다. 검사 자체의 연산·메모리 활동이 결함 발생 조건을 강화할 수 있고, 발생한 손상이 원래보다 더 잘 보일 수도 있다. 실제 사례에서 어느 효과가 지배적인지는 대조 실험과 추적 자료로 판별해야 한다.

### preemption을 허용하는 이유

계산 중간에 인터럽트와 스케줄링이 개입하면, 레지스터의 중간 상태가 저장·복원되는 경로와 그 상태를 담는 메모리도 시험에 관여한다. ARM64 Linux의 예외 진입·복귀는 범용 레지스터를 저장·복원한다. 다만 모든 CPU 상태가 같은 규칙으로 보존되는 것은 아니므로 이 구현은 범용 레지스터만 사용하며 FP/SIMD나 플랫폼 예약 레지스터를 건드리지 않는다. [4, 5]

선점은 제거할 잡음이 아니라 의도한 시험 조건이다. 따라서 프로브 전체를 spinlock, IRQ 차단 또는 preempt_disable로 감싸지 않는다. 실제 선점 지점은 커널 설정과 문맥에 좌우된다.

---page---

# 2. 검사 알고리즘과 불변 조건

버퍼 크기를 B 바이트, 비트 수를 N=8B=2^m으로 둔다. 공유 엔진은 B=64 바이트부터 128 MiB까지의 2의 거듭제곱 크기를 지원한다. 명령행·모듈 인터페이스는 KiB 단위를 사용하므로 최소값은 1 KiB이다. 초기 버퍼는 0xff이며 첫 방향의 기대 비트는 1이다.

### 한 방향의 검사 주기

1. 비영 seed에서 최대 길이 LFSR를 진행한다. 점화식은 오른쪽 시프트 Galois 형식이다.
2. LFSR가 가리키는 비트를 읽고 현재 방향의 기대값과 비교한다.
3. 읽은 바이트와 인덱스로 64비트 token을 만들고 ARM64 GPR 의존 연쇄를 통과시킨다. 원래 token과 같은지 확인한다.
4. 연쇄를 통과한 값의 하위 바이트에서 선택한 비트를 반전해 저장한다.
5. 비영 인덱스 N-1개를 방문한 뒤 LFSR가 seed로 복귀했는지 확인하고, 인덱스 0을 별도로 처리한다.
6. 전체 B 바이트가 기대 종료값인지 읽어 확인한다. 성공하면 방향을 바꾸고 같은 버퍼에서 다음 주기를 시작한다.

```text
L' = (L >> 1) XOR ((0 - (L AND 1)) AND taps[m])
bit_index = L'                     # N-1 nonzero indices
then visit bit_index = 0           # explicit final visit
1 -> 0 walk -> verify all 0x00 -> 0 -> 1 walk -> verify all 0xff
```

정상적인 상태와 연산을 가정하면 한 주기는 모든 버퍼 비트를 한 번씩 반전하고, 모든 바이트를 한 번씩 검증한다. 비용은 초기화를 제외하고 N+B=9B개의 프로브 연산이다. 두 주기를 완료하면 버퍼는 다시 0xff가 된다. 종료 검증까지 마쳐야 완료 주기로 계산한다.

### LFSR가 보장하는 것

LFSR는 방문 순서와 중복 없는 비영 인덱스 순회를 제공한다. seed 변경은 같은 주기의 시작 위치 변경이며 독립적인 무작위 순열이 아니다. 이 성질은 SoC 전체 상태 공간이나 명령 n-gram의 포괄성을 뜻하지 않는다. [2]

원래 표의 14비트 mask 0x201d는 이 점화식에서 주기가 126이었다. 2 KiB 버퍼의 정상 시험도 중복 방문으로 실패할 수 있다. 재작성에서는 0x3802로 교체하고, 지원하는 22개 길이 모두에 대해 선형 변환의 거듭제곱과 주기 소인수 검사를 수행했다. [10]

---page---

# 3. 데이터 의존성과 실행 계약

ARM64 경로의 token은 읽은 바이트를 하위 8비트에, 인덱스에서 만든 변화하는 패턴을 상위 비트에 담는다. 이를 보수·회전·이동 명령의 의존 연쇄로 전달한다. 정상 결과는 입력과 같지만, 컴파일러가 연쇄 전체를 항등식으로 제거하지 못하도록 asm으로 명시한다. 결과를 검사한 뒤 그 결과에서 실제 저장 바이트를 만든다.

단순히 레지스터 여러 개를 읽는 것과 달리, 앞 단계의 값이 뒤 단계의 입력이다. 그러나 모든 시스템 연산을 하나의 완전한 의존 연쇄로 만든 것은 아니다. 이 설계가 특정 마이크로아키텍처의 모든 저장소·실행 유닛을 자극하거나, 중간 오류의 전파를 항상 보장하지도 않는다.

### 컴파일러와의 계약

고정 scratch 레지스터 x9~x14를 모두 clobber에 선언하고, 출력에는 early-clobber 제약을 사용한다. x18과 FP/SIMD는 사용하지 않는다. 원래 구현처럼 입력 전용 피연산자를 몰래 변경하거나, 컴파일러에 알리지 않고 레지스터를 덮어쓰지 않는다. asm volatile은 최적화 제약이며 선점 방지 장치가 아니다. [3]

### 실행 모드

| 경로 | 상태의 위치와 의미 |
|---|---|
| Linux 커널 모듈 | worker마다 private vmalloc 버퍼와 검사 cursor; 커널 스레드 문맥에서 실행 |
| ARM64 사용자 프로세스 | 같은 GPR 연쇄와 엔진; 사용자 프로세스의 스케줄링·주소 공간에서 실행 |
| Portable C | 같은 의미의 변환과 메모리 검사; ARM64 레지스터 경로와 동등한 물리적 검증은 아님 |

chunk는 정지·freezer·상태 게시 사이의 연산 예산이다. 원자적 구간이나 강제 선점 주기가 아니다. chunk 사이의 cond_resched 또는 사용자 공간 sched_yield는 실행 기회를 양보하지만, 연산 중간의 비동기 선점을 대신하지 않는다.

worker마다 메모리를 분리해 검사기 내부의 데이터 경쟁을 피한다. 이는 제품의 공유 메모리 경쟁을 자동 검사한다는 뜻이 아니다. 필요한 경쟁·통신·전원 전이는 외부 QA 시나리오가 만들어야 한다.

---page---

# 4. sleep/wakeup과 지속되는 검사 상태

핵심은 검사 버퍼와 진행 상태를 새로 만들지 않고 중단·재개하는 것이다. 현재 재작성은 각 worker의 버퍼, LFSR 상태, 방문 수, 검증 위치 및 방향을 유지한다. 깨어난 직후 memset으로 덮어쓰지 않으므로, 잠든 동안 남은 손상이 다음 읽기나 주기 종료 검사에 나타날 기회를 보존한다.

### 시스템 suspend와 선점은 다르다

일반적인 선점은 실행 중인 task를 잠시 중단한다. system suspend에는 task freezer, 장치 suspend, CPU·플랫폼 전환 등 별도 단계가 있다. 실제 CPU가 전원이 꺼진 상태에서 소프트웨어 연쇄가 실행되는 것은 아니다. 검사는 보존되거나 복원된 상태를 재개 후 관찰한다. [5, 6]

모듈의 기본 freezable=1은 system-suspend freezer에 협조한다. worker는 chunk 경계에서 정지/freezer 요청을 확인하고, 이미 정해진 주기를 마친 대기 worker도 freezer에 협조한다. 반면 freezable=0은 PM 전환 중 실행 가능한 구간을 달리하는 실험 설정이다. 원래 코드의 실행 조건과 동일하다고 가정해서는 안 된다.

### PM 관측의 해석

모듈은 system suspend/hibernation의 prepare 및 post 통지 횟수를 기록한다. 이것은 요청·복귀 경로의 관측값이다. 전환이 중간에 취소될 수도 있으므로 통지 쌍이 있다고 원하는 하드웨어 저전력 상태에 도달했다고 판정하지 않는다. runtime PM과 CPU idle은 이 카운터에 포함되지 않는다.

외부 QA는 대상 BSP가 제공하는 PM trace, residency counter, serial log 또는 보드 계측과 함께 해석해야 한다. 버퍼의 생존 기간 안에서 어떤 전이가 실제 발생했는지도 확인한다.

### 부하를 높이는 것만으로 충분하지 않다

지속적인 부하가 idle 진입이나 gating을 막으면 목표 조건을 오히려 줄일 수 있다. 작은 캐시 상주 작업 집합, 더 큰 작업 집합, pause가 있는 실행, freeze 여부를 분리해 비교한다. 어떤 조건이 유리한지는 실측 문제이며 이 백서는 보편적인 최적값을 제시하지 않는다.

---page---

# 5. 실패 관측과 검출 한계

재작성은 의도적인 잘못된 주소 접근으로 crash를 만들지 않는다. 불일치를 발견하면 첫 오류를 고정하고, 오류 종류·worker·seed·주기·위치·기대값·관측값을 기록한다. 다른 worker도 chunk 경계에서 정지한다. 커널의 panic_on_error=1을 선택하면 첫 오류 기록 뒤 panic을 발생시켜 외부 QA가 감지할 수 있다. 기본값은 정지와 기록이다.

| 오류 | 관측 내용 |
|---|---|
| data_error / walk | 방문한 비트가 기대한 0 또는 1과 다름 |
| register_error | GPR 연쇄의 64비트 출력이 입력과 다름 |
| data_error / verify | 순회 뒤 읽은 바이트가 0x00 또는 0xff와 다름 |
| state_error | 검사한 cursor 범위·LFSR 복귀 등 상태 조건 위반 |
| 외부 crash / hang | 프로브 보고 전 중단; 별도의 watchdog·로그 수집이 필요 |

이 오류 분류는 관측 지점을 표현한다. register_error가 반드시 물리 레지스터 불량을 뜻하지 않고, data_error가 반드시 DRAM 결함을 뜻하지도 않는다. 컴파일러, 검사기, kernel/BSP, 주소 변환, 캐시, 메모리 또는 환경이 원인일 수 있다.

### 남아 있는 한계

- 검사기를 포함한 시스템 전체가 신뢰 기반이다. 검사 상태나 비교 코드가 동시에 손상되면 오류가 숨을 수 있다.
- 방문 후 생긴 손상은 종료 검사로 일부 보완하지만, 검증을 이미 지난 위치의 손상은 이후 검사까지 남아야 보인다. 소실·상쇄되는 일시 오류를 모두 잡지는 못한다.
- 버퍼 접근이 cache hit이면 DRAM을 읽지 않을 수 있다. 강제 cache flush나 물리 DRAM 셀 순회는 구현하지 않았다.
- vmalloc 버퍼는 사용자 공간 swap workload가 아니다. 페이지 테이블이나 TLB 전체의 포괄성도 보장하지 않는다.
- 대상 제품의 데이터·보안 메모리를 자동으로 읽거나 검사하지 않는다. 제품 고유의 정답 검사와 경계 검증이 필요하다.

오류 전파와 관측 가능성은 테스트 연구에서 다루는 별도의 문제다. 결함에 도달하는 것만으로 결과에 실패가 나타나는 것은 아니며, 중간 상태 손상이 가려지는 fault masking도 고려해야 한다. [7]

---page---

# 6. 확률 모델을 어떻게 해석할 것인가

원안은 연산의 논리적 의존성을 길게 연결하면 성공 확률이 누적해서 낮아져 작은 오류가 더 쉽게 crash로 드러난다는 직관을 제시했다. 이 직관은 검사 가능성에 관한 가설로 유용하지만, 시스템 전체의 신뢰도를 명령 1회의 성공 확률로 직접 대입할 수는 없다. [1]

### 발생과 관측을 분리한다

고정된 QA 시나리오 W에서 A를 목표 결함 조건에 도달하는 사건, E를 그 조건에서 상태가 잘못되는 사건, O를 그 손상이 검사 결과에 드러나는 사건으로 두면, 해당 경로의 검출 사건 D는 다음처럼 분해할 수 있다.

```text
P(D | W) = P(A | W) * P(E | A, W) * P(O | E, A, W)
```

이는 조건부 확률의 분해이며 독립성 가정이 아니다. BITOXIN의 활동은 세 항 모두에 영향을 줄 수 있다. 어떤 항이 개선되었는지는 실험으로 분리해야 한다. 단순한 crash 수 증가만으로 대상 결함의 발생률 증가를 주장할 수 없다.

### 독립·동일 확률은 특별한 경우다

각 기회에서 검출될 확률이 q이고 서로 독립이라면, N번 중 한 번 이상 검출할 확률은 1-(1-q)^N이다. q=10^-6이라는 가정 아래 50%에 이르는 N은 약 693,147이다. 이 수치는 예시 계산이며 명령 수 기반의 실제 검출 시간 보장이 아니다.

일반적으로 q_i를 앞선 기회에서 검출되지 않았다는 조건 아래 i번째에 검출될 확률로 두면 다음 식을 쓸 수 있다. 그러나 실제 q_i를 알지 못하면 수치 예측은 할 수 없다.

```text
P(detected by N) = 1 - product_i(1 - q_i)
q_i = P(D_i | no earlier detection, W)
```

전압·온도·PM 상태와 공통 원인 때문에 오류가 상관될 수 있다. 데이터 의존성을 넣었다는 사실은 확률적 독립성을 만들지 않는다. 또한 상태별 성공 확률의 가중평균인 전체 성공 확률은 그 최솟값과 최댓값 사이에 있으며, 모든 상태별 확률보다 크다고 둘 수 없다.

실무적으로는 명령당 추정 신뢰도보다 첫 유효 실패까지의 시간, 단위 장비 시간당 확인된 결함, 재현율과 원인 분석 소요 시간을 측정하는 편이 직접적이다.

---page---

# 7. 이번 재작성의 검증 증거

아래는 재작성 과정에서 수행한 소프트웨어 검사다. 실제 보드에서 전원 결함을 재현했다는 증거와 구분한다. 정확한 소스 해시는 배포본의 source-manifest.sha256, 상세 기록은 docs/verification.md에 남긴다. [10]

| 검증 항목 | 결과와 범위 |
|---|---|
| macOS ARM64 native | 최적화 빌드, 실제 GPR backend 및 portable backend 테스트 통과 |
| ASan / UBSan | 호스트와 Linux ARM64에서 테스트 통과; asm 내부는 계측 범위 밖 |
| LFSR | 9~30비트 22개 mask의 최대 주기 검사 통과 |
| GPR 연쇄 | 10,128개 입력 패턴의 항등성 확인 |
| 오류 검출 | 방문 전·후 메모리 손상, 반대 방향 손상, 시험용 연쇄 출력 손상 검출 |
| 실행 제어 | chunk 간 상태 유지, 정확한 주기 수, 인자 거부, signal 중단 구분 |
| 커널 빌드 | Linux 6.1.0-53 ARM64 헤더, W=1 모듈 빌드 통과 |
| ARM64 가상 커널 | 유한 주기 완료, 실행 중·완료 후 freezer, 상태 재개, 5회 반복 load/unload 통과 |
| 실제 제품·보드 | Compuon 적용, HESM PM/DDR 시험, 과거 vendor 재현은 미실행 |

### 정상 시스템에서 거짓 실패를 만들던 조건

원래 hook 함수의 반복 조건은 4095 주기를 4096회 실행해 이미 지운 비트를 다시 읽었다. 반면 작성자가 실제 사용한 별도 스레드 경로는 이 경계 오류가 없었다. 재작성은 사용 목적에 맞춰 hook API를 제거하고 독립 worker 구조로 정리했다.

별도로 발견한 14비트 mask 문제는 2 KiB 설정에서 실제 순회 중복을 만들었다. 수정 전 검사가 실패하는 것을 확인하고, 수정 후 전체 주기 검사를 통과시켰다. 이 두 문제를 과거 특정 BSP 사례의 원인으로 단정하지 않는다.

### 증거의 해상도

메모리에 의도적으로 잘못된 값을 놓거나 연쇄의 출력을 대체한 테스트는 검사기가 해당 오류를 알아채는지 검증한다. 실제 전원 sequence가 그 오류를 더 자주 만드는지는 검증하지 않는다. 에뮬레이터의 ARM64 명령 실행과 가상 커널 동작도 실제 칩셋·DDR의 전기적 특성을 재현하지 않는다.

가상 커널의 PM 시험은 pm_test=freezer로 수행했다. 실제 하드웨어 sleep 이전에 돌아오는 시험이므로, PM 통지·task 동결·재개 경로의 증거이지 물리적 suspend/resume 증거가 아니다.

---page---

# 8. 개념을 제품 QA로 옮기고 평가하기

차용할 단위는 커널 모듈이 아니라 검사 구조다. 제품의 실제 상태를 의존하는 연산에 계속 전달하고, 그 상태가 살아 있는 동안 허용된 사건을 끼워 넣는다. 독립된 기준 모델과 비교하여 값·수명·요청 식별의 어긋남을 드러낸다. 사건 순서 포괄성은 별도로 설계할 수 있으며, LFSR 버퍼 순회와 같은 개념은 아니다. [13]

### 공통 실행 구조

1. 알려진 제품 상태와 독립된 기대 상태를 준비한다.
2. 제품은 직전의 실제 결과로 다음 연산을 수행하고, 기준 모델은 같은 의도된 연산을 따로 계산한다.
3. 지원되는 스케줄링·소유권·세션·통신 경계에서 중단과 재개를 배치한다. PM은 가능한 조건 중 하나다.
4. 중간 검사와 최종 검사를 함께 둔다. 첫 불일치의 연산 번호, 기대값, 실제값과 사건 이력을 남긴다.

실제 결과로 기대값을 갱신하거나 매 단계 정답으로 객체를 재생성하면 손상을 숨길 수 있다. 0 곱셈처럼 정보를 지우는 연산과 서로 상쇄되는 역연산도 주의한다. 항등 관계·왕복 검사는 유용하지만 독립된 정답과 다양한 중간 검사를 대신하지 않는다. [7]

### 무엇과 비교할 것인가

| 비교군 | 관측할 기여 |
|---|---|
| A: 독립된 짧은 검사 | 기존 기능 검사 기준선 |
| B: 상태를 이어 쓰는 검사 | 이력·연산 의존성의 효과 |
| C: B + 허용된 사건 교란 | 상태 전이와 타이밍 조합의 효과 |

연산 수·종류·관측 시간과 자원 예산을 가능한 한 맞춘다. 길어진 시험이 더 많은 연산을 수행했다는 이유만으로 의존성의 효과라고 판단하지 않는다. 통제된 시험용 손상 주입은 검출 경로를 검증하지만 실제 결함의 발생 빈도를 알려 주지는 않는다.

### 증거와 판정

빌드·설정·fixture·seed·연산열·사건열·기대값·실제값을 보존한다. seed는 연산 순서를 재현할 뿐 스케줄링까지 재현하지 않는다. 실패열을 줄일 때에도 오류를 만드는 상태 이력을 유지한다.

고유 확인 결함, 거짓 실패, 첫 유효 실패까지의 시간, 재현 분모와 실행 비용을 보고한다. 실패하지 않은 실행도 자료에 포함한다. 허용되지 않은 데이터 경쟁을 제품 결함으로 오인하지 않도록 동기화 계약과 예상 거부 결과를 명시한다. 제품 적용 효과는 앞으로 이 비교로 측정해야 한다.

---page---

# 9. Compuon: 보호 값의 이력을 이어 검사하기

요청된 compuon-dev 경로는 현재 환경에 없으므로 인접한 compuon/core를 잠정 참조했다. 이 절의 출발점은 기존 산술·복사·세션 수명 테스트다. 실제 적용 전 대상 저장소와 빌드 설정을 확인해야 한다. 참조한 Core HEAD는 517f1a1b1206212bb15355e0731bf2d9fb81de17이다. [11]

### 실제 보호 객체가 다음 연산의 입력이 된다

짧은 산술 검사를 긴 의존 연산열로 확장한다. 보호 객체를 계속 사용하고, 별도 기준 모델이 동일한 연산의 기대값을 계산한다. 예를 들어 다음 연산열은 값과 복사 독립성을 함께 검사한다.

```text
protected x = 37; reference r = 37
x += 11; r += 11
copy x to y; independently copy r to s
[permitted scheduling boundary]
y *= 3; s *= 3
x -= 5; r -= 5
verify protected x == 43; protected y == 144
continue from these objects
```

정수 범위를 제한해 검사기 자체의 overflow를 피한다. 평문 cache를 가진 backend에서는 cache 값만 확인하지 말고 실제 보호 상태의 검증 경로도 확인한다. deferred 테스트는 세션 키를 통한 검증 경로를 보여 준다. 보호 기능을 끈 빌드와 보호 빌드의 결과를 구분한다.

### 세션 전이는 계약에 따라 연결한다

init·rekey·shutdown 뒤 어떤 객체가 유효한지는 제품 계약으로 정한다. 이전 handle이 무효화되는 전이라면 예상 거부를 검사하고 다음 세대를 만든다. 보존을 약속한 전이라면 같은 상태로 계산을 이어 간다. 모든 기능을 비활성화해도 통과하는 시험이 되지 않도록 정상 동작 대조 검사도 둔다.

기존의 0 항등식·identity fold 검사는 그 성질을 확인하는 데 유효하다. 다만 긴 오류 탐색 연산열을 0이나 상쇄 연산으로만 구성하면 손상이 사라질 수 있다. 다양한 비영 값, 중간 비교, 통제된 손상 주입으로 오류가 실제 검증에 도달하는지 확인한다.

첫 구현 단위는 기존 테스트 안의 seed 기반 연산열 생성기와 독립된 값·수명 모델이다. 별도 Linux 모듈이나 runtime hook은 필요하지 않다. 이 제안은 아직 제품에 구현되지 않았으며, 통과가 암호학적 안전성이나 anti-cheat 강도를 입증하지도 않는다.

---page---

# 10. HESM: 요청과 결과의 연결을 검사하기

HESM에서는 실제 요청·공유 버퍼·세션 상태가 실행과 응답까지 이어지는 관계를 검사 대상으로 삼는다. 열람한 작업 트리는 수정 상태였으므로 HEAD만으로 참조 내용을 재현할 수 없다. 이 절은 session·shared window·CKKS fixture 테스트에 근거한 확장 제안이다. [12]

### 연결된 트랜잭션을 유지한다

기존 session fixture에는 BEGIN → WRITE_REF/WRITE → EXECUTE → READ와 정답 비교가 있다. 알려진 abcdef 입력에 fedcba를 기대하는 사례, 하나의 입력 tag 아래 WRITE_REF와 WRITE를 혼합하는 사례가 출발점이다.

```text
known input + independent expected result
  -> BEGIN -> WRITE_REF / WRITE -> EXECUTE -> READ
  -> check request identity, status, length and expected bytes
  -> distinct next input; retain service and buffer history
```

매번 서비스를 초기화하지 않고 여러 트랜잭션을 연결한다. 인접 요청에 서로 다른 입력을 사용하면 이전 결과·길이·식별자의 잘못된 재사용을 관측하기 쉽다. 허용된 분할 전송, descriptor offset, 버퍼 재사용과 소유권 인계를 바꾸면서 요청과 결과의 대응을 유지하는지 검사한다.

### 값과 상태 전이를 각각 판정한다

| 검사 대상 | 독립된 판정 기준 |
|---|---|
| 세션·요청 | 상태 모델에 따른 허용 전이, 거부 상태와 거부 후 영향 |
| 공유 버퍼 | 범위·소유권 계약 및 실제 전송된 입력의 정합성 |
| 암호 연산 | 공개 fixture의 정답; 결정적 계수·byte는 정확히 비교 |
| CKKS 복호 값 | 해당 profile의 scale·허용 오차로 근사 결과 비교 |
| 키 수명 | 시험 키의 세대와 문서화된 LOAD/REVOKE 결과 |

지연·retry·abort·reconnect는 계약별로 성공 또는 거부를 명시한다. 모든 중단이 투명하게 복구되어야 한다고 가정하지 않는다. 미검증 USB/PM 전이나 전원 상실 후 키 수명은 별도 탐색 대상이다. 왕복 변환만으로 공유된 구현 오류를 놓치지 않도록 알려진 정답이나 독립 구현을 유지한다.

첫 적용점은 host session fixture의 다중 트랜잭션 검사이며, 같은 판정 기준을 실제 통신·암호 profile로 확장한다. 시험용 손상은 소유권이 정해진 test buffer나 시험 인터페이스에 주입한다. 별도 A35 메모리 프로브를 배치하는 제안이 아니다. 실제 제품 통합과 보드 효과는 아직 측정하지 않았다.

---page---

# 11. 시스템 프로브 참조 구현의 실행

커널 모듈은 bitoxin_qa.ko이며, 기존 burst/hook/mixed 제어 대신 load-time 설정을 사용한다. 정적 구성을 택해 실행 중 메모리 크기·worker 수 변경이 검사 상태를 흔드는 문제를 줄였다. 설정 변경은 unload/reload로 수행한다. 상세 명령과 exit code는 README에 있다. [10]

```text
make module KDIR=<target BSP kernel build tree>
insmod bitoxin_qa.ko mem_kib=1024 threads=2 seed=1 passes=0
cat /sys/kernel/debug/bitoxin/status
... external QA campaign ...
cat /sys/kernel/debug/bitoxin/status > final-status.json
rmmod bitoxin_qa
```

| 항목 | 기본값과 의미 |
|---|---|
| mem_kib / threads | worker당 1024 KiB / 1개; 합계 256 MiB 상한 |
| seed / passes | seed 1; 모듈 0=계속, 사용자 runner는 기본 2주기 |
| chunk / pause_ms | 4096 연산 / 0 ms; 중단·관측 지연과 부하에 영향 |
| freezable | 1; 상태를 보존하며 system-suspend freezer에 협조 |
| panic_on_error | 0; 명시적으로 1을 선택하면 오류 기록 후 panic |

debugfs 상태는 worker별로 일관된 snapshot이며 동시에 찍힌 전역 snapshot은 아니다. 정지·완료 상태에서도 버퍼는 unload까지 유지된다. 상태 파일은 unload 전에 수집한다. debugfs가 마운트되어 있는지, 대상 kernel의 설정·module 서명이 적재를 허용하는지 확인한다. 커널 build tree는 실행할 BSP와 일치해야 한다. [9]

관측 체계는 프로브 외부에도 있어야 한다. 전원이 끊기거나 kernel이 멈추면 JSON과 printk가 남지 않을 수 있다. serial, pstore, watchdog 및 외부 실행기의 boot ID·시각을 결합한다. 오류 뒤 panic을 사용하더라도 기록이 영구 저장된다는 보장은 없다.

### 다음 검증 단계

시스템 프로브 자체의 후속 검증은 대상 BSP의 실행·PM 도달·대조 실험이다. 제품에 개념을 차용하는 후속 작업은 9~10절의 연산열과 기준 모델을 해당 테스트에 구현하는 것이다. 두 작업은 별개이며, 이 모듈의 검증 결과가 제품 적용의 증거가 되지는 않는다.

---page---

# 참고자료와 출처

[1] 작성자 제공. “Feasibility of the algorithm accelerating unknown system vulnerabilities to be exposed as an irreversible crash”, 첨부 PDF 3쪽 및 본 대화의 현장 경험 설명. 원본 파일명 bitoxin_20261005.pdf. 비교군·반복 횟수가 있는 실험 보고서는 첨부되지 않았다.

[2] Peter Alfke / Xilinx. Efficient Shift Registers, LFSR Counters, and Long Pseudo-Random Sequence Generators, XAPP052. LFSR 배경 자료이며 본 구현의 모든 mask는 별도 검증했다.
https://docs.amd.com/v/u/en-US/xapp052

[3] GCC. Extended Asm: input/output operands, early-clobber and clobbers.
https://gcc.gnu.org/onlinedocs/gcc/Extended-Asm.html

[4] Linux v4.14 ARM64. arch/arm64/kernel/entry.S. 범용 레지스터의 예외 진입·복귀 경로.
https://github.com/torvalds/linux/blob/v4.14/arch/arm64/kernel/entry.S

[5] Linux kernel documentation. Proper Locking Under a Preemptible Kernel.
https://docs.kernel.org/locking/preempt-locking.html

[6] Linux kernel documentation. Freezing of tasks; System Suspend Code Flows.
https://docs.kernel.org/power/freezing-of-tasks.html
https://docs.kernel.org/admin-guide/pm/suspend-flows.html

[7] Abou Assi et al. How detrimental is coincidental correctness to coverage-based fault detection and localization? An empirical study. Software Testing, Verification and Reliability, 2021. DOI: 10.1002/stvr.1762. 오류 전파·masking 논의의 배경이며 BITOXIN의 실험 결과는 아니다.
https://doi.org/10.1002/stvr.1762

[8] stressapptest 프로젝트. 메모리·I/O 트래픽과 데이터 검사를 이용한 스트레스 시험 설계.
https://github.com/stressapptest/stressapptest

[9] Linux kernel documentation. Building External Modules.
https://docs.kernel.org/kbuild/modules.html

[10] BITOXIN 2 소스, 테스트 및 docs/verification.md. 원본 기준 commit: 53203f75ab0362924f21299af56ceacc0d1d86b1. 재작성된 파일은 함께 제공한 source-manifest.sha256으로 식별한다.

[11] 로컬 Compuon Core README, tests/test_compuon_deferred.cpp, test_identity_arithmetic.cpp, test_api_lifecycle.cpp, test_sync_protocol.cpp. Core HEAD: 517f1a1b1206212bb15355e0731bf2d9fb81de17. 요청 경로 compuon-dev 대신 인접 compuon을 잠정 참조했다.

[12] 로컬 HESM README, tests/session_test.c, shared_window_test.c, ckks_v2l1w_service_test.c, ckks_v2l1w_kernel_test.c, ckks_v2l1w_tools_test.py, include/hesm/tfm_ops.h. HEAD: d0671cc637d57673516b8141bf7eb82340565073, 수정된 작업 트리에서 열람. 제품 적용 시험은 미실행.

[13] Kuhn, Higdon, Lawrence, Kacker, Lei. Combinatorial Methods for Event Sequence Testing, ICST 2012. DOI: 10.1109/ICST.2012.147. 외부 QA 사건 순서 설계를 확장할 때의 참고자료이며, 버퍼 LFSR 순회와는 다른 포괄성 개념이다.
https://www.nist.gov/publications/combinatorial-methods-event-sequence-testing?pub_id=906770

웹 자료 열람일: 2026-10-05. 문서는 구현 설명·검증 기록·적용 제안을 구분하며, 새 데이터가 생기면 그 구분을 유지한 채 개정한다.
