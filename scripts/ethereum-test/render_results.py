import argparse
import json
import sys


# Interpolate the background color based on the ratio
def interpolate_color(ratio):
    # Extract RGB components from each color
    start_color = (0xEF, 0x8B, 0x9F)
    middle_color = (0xFF, 0xAE, 0x42)
    end_color = (0x8E, 0xF2, 0x85)
    start_r, start_g, start_b = start_color
    middle_r, middle_g, middle_b = middle_color
    end_r, end_g, end_b = end_color
    # Interpolate between start and middle colors
    interpolated_r = int(start_r + (middle_r - start_r) * ratio)
    interpolated_g = int(start_g + (middle_g - start_g) * ratio)
    interpolated_b = int(start_b + (middle_b - start_b) * ratio)
    # Interpolate between middle and end colors
    interpolated_r2 = int(middle_r + (end_r - middle_r) * ratio)
    interpolated_g2 = int(middle_g + (end_g - middle_g) * ratio)
    interpolated_b2 = int(middle_b + (end_b - middle_b) * ratio)
    # Combine the two interpolated colors
    final_r = int(interpolated_r + (interpolated_r2 - interpolated_r) * ratio)
    final_g = int(interpolated_g + (interpolated_g2 - interpolated_g) * ratio)
    final_b = int(interpolated_b + (interpolated_b2 - interpolated_b) * ratio)
    return f"rgb({final_r}, {final_g}, {final_b})"


def display_summary(json_data):
    # Generate HTML
    html = f"""
    <head>
        <script src="https://code.jquery.com/jquery-3.6.0.min.js"></script>
        <script>
        $(document).ready(function() {{
          $("#clickableTable tr").click(function() {{
            window.location = $(this).data("href");
          }});
        }});
        </script>
    </head>
    <body>

    <table id="clickableTable">
        <tr>
            <th>Test Suite Name</th>
            <th>Tests Passed</th>
        </tr>
    """
    for test_suite_name in json_data:
        passed_tests = sum(
            1
            for test_data in json_data[test_suite_name].values()
            if test_data["actual"] == "PASS"
        )
        total_tests = len(json_data[test_suite_name])
        ratio = float(passed_tests / total_tests)
        html += f"""
          <tr style="cursor:pointer;background-color:{interpolate_color(ratio)}" data-href="#link_{test_suite_name}">
              <td>
              {test_suite_name}
              </td>
              <td style="text-decoratio:none">
              {passed_tests}/{total_tests}
              </td>
          </tr>
        """

    html += """</table><hr></body> """
    return html


def display_test_results(test_suite_name, json_data):
    # Calculate the number of tests passed and total number of tests
    passed_tests = sum(
        1
        for test_data in json_data[test_suite_name].values()
        if test_data["actual"] == "PASS"
    )
    total_tests = len(json_data[test_suite_name])

    ratio_passed = float(passed_tests / total_tests)

    # Generate HTML
    html = f"""
      <head>
          <script>
            function toggleTable(id) {{
                var table = document.getElementById(id);
                var content = table;//;.nextElementSibling;
                if (content.style.display === "none") {{
                    content.style.display = "block";
                }} else {{
                    content.style.display = "none";
                }}
            }}
          </script>
      </head>
      <body>

      <div onclick="toggleTable('testTable_{test_suite_name}')" style="cursor:pointer;">
      <h3 id="link_{test_suite_name}" class="collapsible" >&#128317; Test Suite: {test_suite_name}</h3>
      <p>Tests Passed: {passed_tests}/{total_tests}<p>

      <table id="testTable_{test_suite_name}" style="display:none">
          <tr>
              <th>Test Name</th>
              <th>Actual</th>
              <th>Expected</th>
              <th>Time (s)</th>
          </tr>
    """

    for test_name, test_data in json_data[test_suite_name].items():
        actual = test_data["actual"]
        expected = test_data["expected"]
        time = test_data["time"]
        # Determine the class for styling based on pass/fail
        row_class = "passed" if actual == "PASS" else "failed"
        html += f"""
          <tr class="{row_class}">
              <td>{test_name}</td>
              <td>{actual}</td>
              <td>{expected}</td>
              <td>{time}</td>
          </tr>
        """

    html += """</table><hr></div></body>"""
    return html


if __name__ == "__main__":
    parser = argparse.ArgumentParser()

    parser.add_argument(
        "--file",
        type=str,
        help="Path to file containing JSON output from gtest_parallel.py",
    )
    parser.add_argument("--summary", action="store_true")
    parser.add_argument("--repo_url", type=str, help="URL of the repo")
    parser.add_argument("--commit", type=str, help="Git commit message")
    parser.add_argument("--date", type=str, help="Date string")

    args = parser.parse_args()
    json_file_path = args.file
    summary = args.summary
    repo_url = args.repo_url
    commit = args.commit
    date = args.date

    try:
        # Read JSON data from the specified file
        with open(json_file_path, "r") as json_file:
            json_data = json.load(json_file)

            html = f"""<!DOCTYPE html><html>
              <style>
                  table {{
                      font-family: Arial, sans-serif;
                      border-collapse: collapse;
                      width: 50%;
                  }}

                  th, td {{
                      border: 1px solid #dddddd;
                      text-align: left;
                      padding: 8px;
                  }}

                  tr:nth-child(even) {{
                      background-color: #f2f2f2;
                  }}

                  tr.passed {{
                      background-color: lightgreen;
                  }}

                  tr.failed {{
                      background-color: lightcoral;
                  }}

                  .collapsible {{
                      cursor: pointer;
                  }}

                  .content {{
                      display:none;
                  }}

              </style>
              <h1>Ethereum Test Coverage - {date}</h1>
              <h2>Total Tests Passed: {
                json_data["num_failures_by_type"]["PASS"]
                }/{
                json_data["num_failures_by_type"]["FAIL"]
                }, Tests Timed Out: {
                json_data["num_failures_by_type"]["TIMEOUT"]
                }</h2>
              <p>Tests run on <a href="{repo_url}/commit/{commit}">{commit}.</a>
              <p>
            """
            html += display_summary(json_data["tests"])
            if not args.summary:
                for key, value in json_data["tests"].items():
                    html += display_test_results(key, json_data["tests"])

            html += """</html>"""
            print(html)

    except FileNotFoundError:
        print(f"Error: File '{json_file_path}' not found.")
        sys.exit(1)
    except json.JSONDecodeError as e:
        print(f"Error: Invalid JSON format in '{json_file_path}': {e}")
        sys.exit(1)
